import os
import sys
import time
import math
import json
import signal
import logging
import socket
from urllib.parse import urlparse
from dataclasses import dataclass, field
from typing import Dict, List, Optional, Set, Tuple

from datetime import datetime, timedelta, time as dtime

import pytz
import requests
import yfinance as yf
from rich.console import Console
from rich.table import Table
from rich.live import Live
import pandas as pd
from collections import deque
import threading
from copy import deepcopy
import io
from datetime import datetime
import os
from fpdf import FPDF  # Add this dependency to requirements.txt if not present
import subprocess

# Optional plotting (Plotly Dash)
ENABLE_DASH = os.getenv("ENABLE_DASH", "1") == "1"
DASH_PORT = int(os.getenv("DASH_PORT", "8050"))
HISTORY_POINTS = int(os.getenv("HISTORY_POINTS", "240"))  # keep last N points per symbol

if ENABLE_DASH:
    try:
        import dash
        from dash import Dash, dcc, html, Input, Output, State
        import plotly.graph_objects as go
        DASH_AVAILABLE = True
    except Exception:
        DASH_AVAILABLE = False
        ENABLE_DASH = False
else:
    DASH_AVAILABLE = False

# Optional public tunnel (ngrok)
ENABLE_TUNNEL = os.getenv("ENABLE_TUNNEL", "1") == "1"
# Prefer Cloudflare Tunnel if enabled
ENABLE_CF_TUNNEL = os.getenv("ENABLE_CF_TUNNEL", "1") == "1"
CLOUDFLARED_PATH = os.getenv("CLOUDFLARED_PATH", "cloudflared")
NGROK_AUTHTOKEN = os.getenv("NGROK_AUTHTOKEN", "")
try:
    from pyngrok import ngrok
    NGROK_AVAILABLE = True
except Exception:
    NGROK_AVAILABLE = False

# Keep references to long-running tunnel processes so they are not garbage
# collected (which can inadvertently terminate the tunnel on some platforms).
TUNNEL_PROCESSES: List[subprocess.Popen] = []


def _drain_process_stdout(proc: subprocess.Popen, label: str) -> None:
    """Continuously drain stdout for a long-running subprocess to avoid deadlocks."""
    if not proc.stdout:
        return

    def _drain() -> None:
        try:
            for line in iter(proc.stdout.readline, ""):
                if not line:
                    break
                logger.debug("%s: %s", label, line.rstrip())
        except Exception as exc:
            logger.debug("stdout drain for %s terminated: %s", label, exc)

    threading.Thread(target=_drain, name=f"{label}_stdout", daemon=True).start()

# Helper to load ngrok token from local file if env not set
# (already defined below if present)
try:
    _load_ngrok_token_from_file
except NameError:
    def _load_ngrok_token_from_file() -> str:
        try:
            token_path = os.path.join(os.getcwd(), 'ngrok_token.txt')
            if os.path.exists(token_path):
                with open(token_path, 'r', encoding='utf-8') as f:
                    return f.read().strip()
        except Exception:
            pass
        return ""

# Start a Cloudflare quick tunnel and return the public URL
def start_cloudflare_tunnel(port: int) -> Optional[str]:
    if not ENABLE_TUNNEL or not ENABLE_CF_TUNNEL:
        return None
    try:
        # cloudflared tunnel --url http://localhost:{port}
        proc = subprocess.Popen(
            [CLOUDFLARED_PATH, "tunnel", "--url", f"http://localhost:{port}", "--no-autoupdate"],
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            text=True,
            bufsize=1,
        )
        public_url: Optional[str] = None
        start_time = time.time()
        while time.time() - start_time < 20:
            line = proc.stdout.readline() if proc.stdout else ""
            if not line:
                if proc.poll() is not None:
                    break
                time.sleep(0.2)
                continue
            logger.debug("cloudflared: %s", line.rstrip())
            if "trycloudflare.com" in line:
                for token in line.split():
                    if token.startswith("http") and "trycloudflare.com" in token:
                        public_url = token.strip()
                        break
            if public_url:
                break

        if not public_url:
            logger.warning("Cloudflare Tunnel did not return a URL in time.")
            try:
                proc.terminate()
            except Exception:
                pass
            return None

        # Give the hostname a little time to propagate. Even if resolution
        # fails now, keep the tunnel alive and return the URL so the caller can
        # retry from their browser shortly afterwards.
        parsed = urlparse(public_url)
        host = parsed.hostname if parsed else None
        if host:
            resolved = False
            for attempt in range(10):
                try:
                    socket.gethostbyname(host)
                    resolved = True
                    break
                except socket.gaierror:
                    time.sleep(1.0)
            if not resolved:
                logger.warning(
                    "Cloudflare Tunnel hostname %s not resolving yet. The URL may take a few seconds to become active.",
                    host,
                )

        # Keep stdout drained so the tunnel process does not block and retain reference.
        _drain_process_stdout(proc, "cloudflared")
        TUNNEL_PROCESSES.append(proc)
        return public_url
    except FileNotFoundError:
        logger.warning("cloudflared not found. Install from https://developers.cloudflare.com/cloudflare-one/connections/connect-networks/downloads/")
        return None
    except Exception as e:
        logger.warning(f"Failed to start Cloudflare tunnel: {e}")
        return None

# Start a public tunnel via ngrok if CF not used/available
def start_public_tunnel(port: int) -> Optional[str]:
    if not ENABLE_TUNNEL:
        return None
    # Prefer CF
    url = start_cloudflare_tunnel(port)
    if url:
        return url
    # Fallback to ngrok
    if not NGROK_AVAILABLE:
        return None
    try:
        token = NGROK_AUTHTOKEN or _load_ngrok_token_from_file()
        if not token:
            logger.warning("Ngrok fallback skipped: no authtoken configured.")
            return None
        if token:
            ngrok.set_auth_token(token)
        for t in ngrok.get_tunnels():
            if f":{port}" in t.config.get('addr',''):
                try:
                    ngrok.disconnect(t.public_url)
                except Exception:
                    pass
        tun = ngrok.connect(port, proto="http")
        return tun.public_url
    except Exception as e:
        logger.warning(f"Failed to start ngrok tunnel: {e}")
        return None

# Global in-memory trade log for all events
TRADE_LOG: List[dict] = []

# Helper function: log event
def log_trade_event(timestamp, symbol, event_type, price, side, qty, entry_price=None, extra=None):
    event = {
        'timestamp': timestamp,
        'symbol': symbol,
        'event_type': event_type,
        'price': price,
        'side': side,
        'qty': qty,
        'entry_price': entry_price,
    }
    if extra:
        event.update(extra)
    TRADE_LOG.append(event)

# Patch: everywhere an event occurs, also call log_trade_event()
# -- For buy/sell entry: in try_entry()
# -- For exit/target/sl: in handle_targets_and_trailing()
# EOD squareoff: also log with exit_type 'EOD'.

# (Below are IN PATCH locations, actual patching to follow)
# try_entry/state.side=\"BUY\": add log_trade_event(now, state.symbol, 'BUY_ENTRY', price, 'BUY', dyn_qty)
# try_entry/state.side=\"SELL\": add log_trade_event(now, state.symbol, 'SELL_ENTRY', price, 'SELL', dyn_qty)
# handle_targets_and_trailing/full exit/target hit: add log_trade_event(now, state.symbol, 'T{idx+1}', tgt, 'BUY', qty_to_exit, entry_price=state.entry_price)
# handle_targets_and_trailing/full exit/stoploss: log_trade_event(now, state.symbol, 'BUY_SL', price, 'BUY', qty_to_exit, entry_price=state.entry_price)
# (analogous for SELL)
# EOD: log PnL for open position as 'EOD_CLOSE'

# At EOD, write summary Excel

def eod_save_summary_excel(trade_log: List[dict], states, last_prices, date_str=None):
    try:
        import os
        from pandas import ExcelWriter
        if not trade_log:
            logger.info("No trades to save in EOD summary.")
            return
        if date_str is None:
            date_str = now_ist().strftime('%Y%m%d')
        summary_dir = "summary"
        os.makedirs(summary_dir, exist_ok=True)
        path = os.path.join(summary_dir, f"summary_events_{date_str}.xlsx")
        df = pd.DataFrame(trade_log)
        # Write all events to first sheet
        with ExcelWriter(path, engine='xlsxwriter') as writer:
            df.to_excel(writer, sheet_name="All Events", index=False)
            # Build summary
            summary_rows = []
            total_pnl = 0
            total_brokerage = 0
            symbols = df['symbol'].unique()
            for sym in symbols:
                for side in ['BUY', 'SELL']:
                    sub = df[(df['symbol']==sym)&(df['side']==side)].sort_values('timestamp')
                    qty_open = 0
                    entry_price = 0
                    rows = []
                    for idx, row in sub.iterrows():
                        event = row['event_type']
                        if event in ['BUY_ENTRY', 'SELL_ENTRY']:
                            qty_open += row['qty']
                            entry_price = row['price']
                        elif event.startswith('T') or event.endswith('SL') or event == 'EOD_CLOSE' or event.startswith('ST'):
                            if entry_price:
                                # For targets/eod/sl
                                if side == 'BUY':
                                    pnl = (row['price'] - entry_price) * row['qty']
                                else:
                                    pnl = (entry_price - row['price']) * row['qty']
                                brokerage = BROKERAGE_FLAT_PER_SIDE + BROKERAGE_FLAT_PER_SIDE
                                total_pnl += pnl
                                total_brokerage += brokerage
                                rows.append(dict(
                                    symbol=sym, side=side, qty=row['qty'], entry_price=entry_price, exit_price=row['price'],
                                    exit_type=event, pnl=pnl, brokerage=brokerage, timestamp=row['timestamp']
                                ))
                                qty_open -= row['qty']
                                if qty_open < 0: qty_open = 0
                                entry_price = 0 if qty_open == 0 else entry_price
                    # If still open position at EOD: close at last price
                    if qty_open > 0 and sym in last_prices:
                        eod_px = last_prices[sym]
                        if entry_price:
                            if side == 'BUY':
                                pnl = (eod_px - entry_price) * qty_open
                            else:
                                pnl = (entry_price - eod_px) * qty_open
                            brokerage = BROKERAGE_FLAT_PER_SIDE + BROKERAGE_FLAT_PER_SIDE
                            total_pnl += pnl
                            total_brokerage += brokerage
                            rows.append(dict(
                                symbol=sym, side=side, qty=qty_open, entry_price=entry_price, exit_price=eod_px,
                                exit_type='EOD_CLOSE', pnl=pnl, brokerage=brokerage, timestamp=now_ist()
                            ))
                    for r in rows:
                        summary_rows.append(r)
            summary_df = pd.DataFrame(summary_rows)
            if not summary_df.empty:
                totals = dict(
                    symbol='TOTAL', side='', qty=summary_df['qty'].sum(),
                    entry_price='', exit_price='', exit_type='',
                    pnl=summary_df['pnl'].sum(), brokerage=summary_df['brokerage'].sum(), timestamp=''
                )
                summary_df = pd.concat([summary_df, pd.DataFrame([totals])], ignore_index=True)
            summary_df.to_excel(writer, sheet_name="EOD Summary", index=False)
        logger.info(f"EOD trade log + summary written to {path}")
    except Exception as e:
        logger.warning(f"Failed to write EOD trade log/summary: {str(e)}")


# ----------------------------
# Configuration
# ----------------------------

IST = pytz.timezone("Asia/Kolkata")
UPDATE_INTERVALS_SECONDS = [1, 2, 5]
BROKERAGE_RATE = 0.0  # deprecated percentage model (kept for compatibility)
BROKERAGE_FLAT_PER_SIDE = 10.0  # ₹10 per execution (entry or exit)
QUANTITY_PER_TRADE = 16  # deprecated fixed model; dynamic sizing used at entry
X_FACTOR_MULTIPLIER = x

# Telegram
TELEGRAM_BOT_TOKEN = os.getenv("TELEGRAM_BOT_TOKEN", "7587307352:AAG6RaiF4gO5I_ZFZ_4b8Gj7dnsu4GtPWFw")
# Default your chat ID so you don't need to set env each run
TELEGRAM_CHAT_ID = os.getenv("TELEGRAM_CHAT_ID", "1376513391")
# Add support for sending alerts to multiple Telegram chat IDs (including Ajay)
TELEGRAM_EXTRA_CHAT_IDS = ["793674804"]


# ----------------------------
# Logging
# ----------------------------

logging.basicConfig(
    level=logging.INFO,
    format="%(asctime)s - %(levelname)s - %(message)s",
    handlers=[logging.StreamHandler(sys.stdout)],
)
logger = logging.getLogger("live_levels")


# ----------------------------
# Stock list (from prior program)
# ----------------------------

STOCKS: List[str] = [
    "HDFCBANK", "KOTAKBANK", "SBIN", "ICICIBANK", "INDUSINDBK",
    "ADANIPORTS", "ADANIENT", "ASIANPAINT", "BAJFINANCE", "DRREDDY",
    "SUNPHARMA", "INFY", "TCS", "TECHM",
    "TITAN", "TATAMOTORS", "RELIANCE", "INDIGO", "JUBLFOOD",
    "BATAINDIA", "PIDILITIND", "ZEEL", "BALKRISIND", "VOLTAS",
    "PEL", "ITC", "BPCL", "BRITANNIA", "HEROMOTOCO",
    "HINDUNILVR", "UPL", "SRF", "TATACONSUM", "BALRAMCHIN",
    "ABFRL", "VEDL", "COFORGE",
]

# ----------------------------
# In-memory price history for charts
# ----------------------------

PRICE_HISTORY: Dict[str, deque] = {}
# Keep a small rolling feed of recent alerts for display in Dash
ALERT_FEED: deque = deque(maxlen=100)
HISTORY_LOCK = threading.Lock()

def init_price_history(symbols: List[str]) -> None:
    with HISTORY_LOCK:
        for s in symbols:
            if s not in PRICE_HISTORY:
                PRICE_HISTORY[s] = deque(maxlen=HISTORY_POINTS)

def append_price_history(symbol: str, ts: datetime, price: float) -> None:
    with HISTORY_LOCK:
        if symbol not in PRICE_HISTORY:
            PRICE_HISTORY[symbol] = deque(maxlen=HISTORY_POINTS)
        PRICE_HISTORY[symbol].append((ts, price))

def record_alert(text: str) -> None:
    # Store alert text with timestamp for dashboard display
    ALERT_FEED.append((now_ist(), text))

def get_recent_alerts(limit: int = 15) -> List[Tuple[datetime, str]]:
    # Return latest alerts (up to limit) in chronological order
    items = list(ALERT_FEED)[-limit:]
    return items

def calculate_eod_analysis() -> dict:
    """Calculate comprehensive EOD analysis from REALIZED_EVENTS."""
    with EVENTS_LOCK:
        all_events = {k: list(v) for k, v in REALIZED_EVENTS.items()}
    
    analysis = {
        'symbols': {},
        'global': {
            'total_realized': 0.0,
            'total_unrealized': 0.0,
            'total_net': 0.0,
            'target_counts': {'T1': 0, 'T2': 0, 'T3': 0, 'T4': 0, 'T5': 0, 'ST1': 0, 'ST2': 0, 'ST3': 0, 'ST4': 0, 'ST5': 0},
            'sl_counts': {'BUY_SL': 0, 'SELL_SL': 0},
            'buy_realized': 0.0,
            'sell_realized': 0.0,
            'buy_unrealized': 0.0,
            'sell_unrealized': 0.0,
        }
    }
    
    for symbol, events in all_events.items():
        sym_data = {
            'realized': 0.0,
            'unrealized': 0.0,
            'total': 0.0,
            'buy_hits': {'T1': 0, 'T2': 0, 'T3': 0, 'T4': 0, 'T5': 0, 'SL': 0},
            'sell_hits': {'ST1': 0, 'ST2': 0, 'ST3': 0, 'ST4': 0, 'ST5': 0, 'SL': 0},
        }
        
        for ev in events:
            if ev['event'] == 'EOD_OPEN':
                sym_data['unrealized'] += ev['net']
                analysis['global']['total_unrealized'] += ev['net']
                if ev['side'] == 'BUY':
                    analysis['global']['buy_unrealized'] += ev['net']
                else:
                    analysis['global']['sell_unrealized'] += ev['net']
            else:
                sym_data['realized'] += ev['net']
                analysis['global']['total_realized'] += ev['net']
                
                if ev['side'] == 'BUY':
                    analysis['global']['buy_realized'] += ev['net']
                    if ev['event'] in ['T1', 'T2', 'T3', 'T4', 'T5']:
                        sym_data['buy_hits'][ev['event']] += 1
                        analysis['global']['target_counts'][ev['event']] += 1
                    elif ev['event'] == 'BUY_SL':
                        sym_data['buy_hits']['SL'] += 1
                        analysis['global']['sl_counts']['BUY_SL'] += 1
                else:
                    analysis['global']['sell_realized'] += ev['net']
                    if ev['event'] in ['ST1', 'ST2', 'ST3', 'ST4', 'ST5']:
                        sym_data['sell_hits'][ev['event']] += 1
                        analysis['global']['target_counts'][ev['event']] += 1
                    elif ev['event'] == 'SELL_SL':
                        sym_data['sell_hits']['SL'] += 1
                        analysis['global']['sl_counts']['SELL_SL'] += 1
        
        sym_data['total'] = sym_data['realized'] + sym_data['unrealized']
        analysis['symbols'][symbol] = sym_data
    
    analysis['global']['total_net'] = analysis['global']['total_realized'] + analysis['global']['total_unrealized']
    
    # Calculate win rate
    total_targets = sum(analysis['global']['target_counts'].values())
    total_sl = sum(analysis['global']['sl_counts'].values())
    total_trades = total_targets + total_sl
    analysis['global']['win_rate'] = (total_targets / total_trades * 100) if total_trades > 0 else 0.0
    
    # Calculate buy vs sell win rates
    buy_targets = sum(analysis['global']['target_counts'][f'T{i}'] for i in range(1, 6))
    buy_sl = analysis['global']['sl_counts']['BUY_SL']
    buy_trades = buy_targets + buy_sl
    analysis['global']['buy_win_rate'] = (buy_targets / buy_trades * 100) if buy_trades > 0 else 0.0
    
    sell_targets = sum(analysis['global']['target_counts'][f'ST{i}'] for i in range(1, 6))
    sell_sl = analysis['global']['sl_counts']['SELL_SL']
    sell_trades = sell_targets + sell_sl
    analysis['global']['sell_win_rate'] = (sell_targets / sell_trades * 100) if sell_trades > 0 else 0.0
    
    return analysis

def get_price_history(symbol: str) -> List[Tuple[datetime, float]]:
    with HISTORY_LOCK:
        dq = PRICE_HISTORY.get(symbol)
        return list(dq) if dq else []


# ----------------------------
# Intraday OHLC fetch (yfinance)
# ----------------------------

VALID_INTERVALS = ["1m", "2m", "5m", "15m", "30m", "60m", "90m"]
INDICATOR_OPTIONS = [
    {"label": "None", "value": "none"},
    {"label": "SMA (20)", "value": "sma20"},
    {"label": "EMA (20)", "value": "ema20"},
    {"label": "Bollinger Bands (20, 2)", "value": "bbands"},
    {"label": "VWAP (session)", "value": "vwap"},
]

_OHLC_CACHE: Dict[Tuple[str, str, str, str], Tuple[float, pd.DataFrame]] = {}

def fetch_intraday_ohlc(symbol: str, interval: str, window: str) -> Optional[pd.DataFrame]:
    if interval not in VALID_INTERVALS:
        return None
    # Cache key also includes date stamp to avoid stale carryover across days
    date_key = now_ist().strftime("%Y%m%d")
    key = (symbol, interval, window, date_key)
    now_ts = time.time()
    cached = _OHLC_CACHE.get(key)
    if cached and (now_ts - cached[0] < 55):  # refresh at most once per minute
        return cached[1]

    try:
        t = yf.Ticker(f"{symbol}.NS")
        # Use 1d period for today windows
        df = t.history(period="1d", interval=interval, auto_adjust=False)
        if df is None or df.empty:
            fallback_period = "5d" if interval in ("1m", "2m", "5m") else "1mo"
            try:
                df = t.history(period=fallback_period, interval=interval, auto_adjust=False)
            except Exception:
                df = None
        if (df is None or df.empty) and interval in ("1m", "2m", "5m"):
            try:
                df = yf.download(
                    tickers=f"{symbol}.NS",
                    period="5d",
                    interval=interval,
                    auto_adjust=False,
                    progress=False,
                    threads=False,
                )
            except Exception:
                df = None
        if df is None or df.empty:
            return None
        if isinstance(df.columns, pd.MultiIndex):
            df.columns = df.columns.get_level_values(0)
        # Localize to IST
        if df.index.tz is None:
            df.index = df.index.tz_localize(pytz.UTC).tz_convert(IST)
        else:
            df.index = df.index.tz_convert(IST)

        if window == "Today":
            start_ts = now_ist().replace(hour=9, minute=15, second=0, microsecond=0)
            df = df.loc[df.index >= start_ts]
        elif window == "6h":
            start_ts = now_ist() - timedelta(hours=6)
            df = df.loc[df.index >= start_ts]
        elif window == "1d":
            # Full session from 09:15 today
            start_ts = now_ist().replace(hour=9, minute=15, second=0, microsecond=0)
            df = df.loc[df.index >= start_ts]

        # Normalize columns
        cols = {c: c.capitalize() for c in df.columns}
        df = df.rename(columns=cols)

        _OHLC_CACHE[key] = (now_ts, df)
        return df
    except Exception as e:
        logger.debug(f"ohlc fetch error {symbol} {interval} {window}: {e}")
        return None


# ----------------------------
# Data classes
# ----------------------------

@dataclass
class Levels:
    previous_close: float
    x: float
    target_step: float  # step for T/ST progression; usually x, special = 0.6 * x
    # buy side
    buy_above: float
    t: List[float]  # t1..t5
    buy_sl: float
    # sell side
    sell_below: float
    st: List[float]  # st1..st5
    sell_sl: float


@dataclass
class SymbolState:
    symbol: str
    levels: Levels
    adjusted_locked: bool = False  # set after 9:30 lock
    last_price: Optional[float] = None
    sent_events: Set[str] = field(default_factory=set)  # de-dup alerts
    in_position: bool = False
    side: Optional[str] = None  # "BUY" or "SELL"
    entry_price: Optional[float] = None
    entry_time: Optional[datetime] = None
    qty_remaining: int = QUANTITY_PER_TRADE
    qty_total: int = QUANTITY_PER_TRADE
    trade_date: Optional[str] = None  # YYYYMMDD of last trade day
    exited_today: bool = False  # block re-entry after full exit until next day
    buy_trailing_sl: Optional[float] = None
    sell_trailing_sl: Optional[float] = None
    last_target_hit_index: int = -1  # -1 means none
    initial_levels: Optional[Levels] = None  # store original levels for comparison


# ----------------------------
# Utilities
# ----------------------------

def now_ist() -> datetime:
    return datetime.now(IST)


def is_between(local_dt: datetime, start_h: int, start_m: int, end_h: int, end_m: int) -> bool:
    s = local_dt.replace(hour=start_h, minute=start_m, second=0, microsecond=0)
    e = local_dt.replace(hour=end_h, minute=end_m, second=0, microsecond=0)
    return s <= local_dt <= e


def market_open(local_dt: datetime) -> bool:
    return is_between(local_dt, 9, 15, 15, 30)


def alerts_allowed(local_dt: datetime) -> bool:
    # No new alerts after 15:15
    cutoff = local_dt.replace(hour=15, minute=15, second=0, microsecond=0)
    return local_dt <= cutoff


def premarket_window(local_dt: datetime) -> bool:
    return is_between(local_dt, 9, 15, 9, 30)


def get_prev_close(symbol: str) -> Optional[float]:
    try:
        now_local = now_ist()
        market_open_dt = now_local.replace(hour=9, minute=15, second=0, microsecond=0)
        market_cutoff = now_local.replace(hour=15, minute=30, second=0, microsecond=0)
        t = yf.Ticker(f"{symbol}.NS")
        # Pull a week of daily bars for robustness across weekends/holidays
        h = t.history(period="10d", interval="1d")
        if h is None or h.empty:
            return None
        # yfinance daily index is date-like; get the latest available trading day
        last_close = float(h["Close"].iloc[-1])
        last_date = h.index[-1].date()
        today_date = now_local.date()
        # After market close: use today's close (should be present as the last row)
        if now_local >= market_cutoff:
            return last_close
        # Before market close (includes pre-open and live session):
        # Use the last fully completed trading day (yesterday). If yfinance already
        # published today's daily row early for any reason, step back one row.
        if last_date == today_date and len(h) >= 2:
            return float(h["Close"].iloc[-2])
        return last_close
    except Exception as e:
        logger.warning(f"prev close error {symbol}: {e}")
        return None


def get_live_price(symbol: str) -> Optional[float]:
    try:
        t = yf.Ticker(f"{symbol}.NS")
        p = t.fast_info.get("lastPrice")
        if not p:
            p = t.info.get("regularMarketPrice")
        if p and p > 0:
            return float(p)
        return None
    except Exception as e:
        logger.debug(f"live price error {symbol}: {e}")
        return None


def calc_levels_for_symbol(symbol: str, prev_close: float) -> Levels:
    x = prev_close * X_FACTOR_MULTIPLIER
    special_symbols = {"RELIANCE", "SBIN", "KOTAKBANK", "ICICIBANK"}
    step = x * 0.6 if symbol in special_symbols else x

    buy_above = prev_close + x
    t1 = buy_above + step
    t2 = t1 + step
    t3 = t2 + step
    t4 = t3 + step
    t5 = t4 + step

    sell_below = prev_close - x
    st1 = sell_below - step
    st2 = st1 - step
    st3 = st2 - step
    st4 = st3 - step
    st5 = st4 - step

    return Levels(
        previous_close=prev_close,
        x=x,
        target_step=step,
        buy_above=buy_above,
        t=[t1, t2, t3, t4, t5],
        buy_sl=buy_above - x,
        sell_below=sell_below,
        st=[st1, st2, st3, st4, st5],
        sell_sl=sell_below + x,
    )


def adjust_levels_premarket(levels: Levels, current_price: float, side: Optional[str] = None) -> Tuple[Levels, Optional[str], Optional[str]]:
    # Returns (new_levels, crossed_level_name, shift_type)
    # shift_type: 'BUY' or 'SELL' or None
    x = levels.x
    step = getattr(levels, 'target_step', x)
    # Deepcopy to avoid reference bugs
    new_levels = deepcopy(levels)

    buy_levels = [levels.buy_above] + list(levels.t)
    sell_levels = [levels.sell_below] + list(levels.st)
    buy_names = ["BUY_ABOVE", "T1", "T2", "T3", "T4", "T5"]
    sell_names = ["SELL_BELOW", "ST1", "ST2", "ST3", "ST4", "ST5"]

    # Sequential shifting, step by step, only one shift per call
    # Buy side
    for idx, lv in enumerate(buy_levels):
        if current_price >= lv:
            if idx == 0:
                # Crossed Buy Above => new Buy Above = old T1, T1 = T2, ..., T4 = T5, T5 = T5 + x
                new_levels.buy_above = levels.t[0]
                for i in range(4):
                    new_levels.t[i] = levels.t[i+1]
                new_levels.t[4] = levels.t[4] + step
                new_levels.buy_sl = new_levels.buy_above - x
                # Also shift SELL side up by step to maintain constant X difference
                new_levels.sell_below = levels.sell_below + step
                for i in range(5):
                    new_levels.st[i] = levels.st[i] + step
                new_levels.sell_sl = new_levels.sell_below + x
                return new_levels, buy_names[idx], 'BUY'
            elif 1 <= idx <= 4:
                # Crossed T1-T4 -> shift corresponding targets
                sh = idx
                for i in range(sh-1, 4):
                    new_levels.t[i] = levels.t[i+1]
                new_levels.t[4] = levels.t[4] + step
                new_levels.buy_sl = new_levels.buy_above - x
                # Also shift SELL side up by step to maintain constant X difference
                new_levels.sell_below = levels.sell_below + step
                for i in range(5):
                    new_levels.st[i] = levels.st[i] + step
                new_levels.sell_sl = new_levels.sell_below + x
                return new_levels, buy_names[idx], 'BUY'
            elif idx == 5:
                # Crossed T5, extend T5
                new_levels.t[4] = levels.t[4] + step
                new_levels.buy_sl = new_levels.buy_above - x
                # Also shift SELL side up by step to maintain constant X difference
                new_levels.sell_below = levels.sell_below + step
                for i in range(5):
                    new_levels.st[i] = levels.st[i] + step
                new_levels.sell_sl = new_levels.sell_below + x
                return new_levels, buy_names[idx], 'BUY'
    # Sell side
    for idx, lv in enumerate(sell_levels):
        if current_price <= lv:
            if idx == 0:
                # Crossed Sell Below => new Sell Below = old ST1, ST1 = ST2, ..., ST4 = ST5, ST5 = ST5 - x
                new_levels.sell_below = levels.st[0]
                for i in range(4):
                    new_levels.st[i] = levels.st[i+1]
                new_levels.st[4] = levels.st[4] - step
                new_levels.sell_sl = new_levels.sell_below + x
                # Also shift BUY side down by step to maintain constant X difference
                new_levels.buy_above = levels.buy_above - step
                for i in range(5):
                    new_levels.t[i] = levels.t[i] - step
                new_levels.buy_sl = new_levels.buy_above - x
                return new_levels, sell_names[idx], 'SELL'
            elif 1 <= idx <= 4:
                sh = idx
                for i in range(sh-1, 4):
                    new_levels.st[i] = levels.st[i+1]
                new_levels.st[4] = levels.st[4] - step
                new_levels.sell_sl = new_levels.sell_below + x
                # Also shift BUY side down by step to maintain constant X difference
                new_levels.buy_above = levels.buy_above - step
                for i in range(5):
                    new_levels.t[i] = levels.t[i] - step
                new_levels.buy_sl = new_levels.buy_above - x
                return new_levels, sell_names[idx], 'SELL'
            elif idx == 5:
                new_levels.st[4] = levels.st[4] - step
                new_levels.sell_sl = new_levels.sell_below + x
                # Also shift BUY side down by step to maintain constant X difference
                new_levels.buy_above = levels.buy_above - step
                for i in range(5):
                    new_levels.t[i] = levels.t[i] - step
                new_levels.buy_sl = new_levels.buy_above - x
                return new_levels, sell_names[idx], 'SELL'
    return levels, None, None


def send_telegram(text: str) -> None:
    if not TELEGRAM_BOT_TOKEN or not TELEGRAM_CHAT_ID:
        # Even if Telegram is not configured, still record alert for dashboard
        record_alert(text)
        return
    try:
        url = f"https://api.telegram.org/bot{TELEGRAM_BOT_TOKEN}/sendMessage"
        # Always send to main + to extra chat ids
        all_chat_ids = [TELEGRAM_CHAT_ID] + TELEGRAM_EXTRA_CHAT_IDS
        for chat_id in all_chat_ids:
            data = {"chat_id": chat_id, "text": text}
            requests.post(url, data=data, timeout=10)
    except Exception as e:
        logger.debug(f"telegram send error: {e}")
    finally:
        # Always mirror to dashboard feed
        record_alert(text)

def _fmt_pct(value: float) -> str:
    sign = "+" if value >= 0 else ""
    return f"{sign}{value:.2f}%"


def _detect_side_from_status(status: str) -> Optional[str]:
    s = status.upper()
    if "BUY" in s:
        return "BUY"
    if "SELL" in s:
        return "SELL"
    # If status mentions a specific level, infer direction
    if any(k in s for k in ["T1", "T2", "T3", "T4", "T5"]):
        return "BUY"
    if any(k in s for k in ["ST1", "ST2", "ST3", "ST4", "ST5"]):
        return "SELL"
    return None


def _build_levels_section(side: str, lv: 'Levels', current_price: float, hit_level: Optional[str]) -> List[str]:
    lines: List[str] = []
    if side == "BUY":
        lines.append("📈 Buy Levels:")
        # Buy Above
        ba_line = f"Buy Above: {lv.buy_above:.2f}"
        lines.append(ba_line)
        # Targets with perc from current price
        for i, tgt in enumerate(lv.t, start=1):
            pct = (tgt - current_price) / current_price * 100.0
            lines.append(
                f"Target {i}: {tgt:.2f} ({_fmt_pct(pct)})"
            )
        # Stop Loss (previous_close)
        sl = lv.buy_sl
        pct_sl = (sl - current_price) / current_price * 100.0
        lines.append(f"Stop Loss: {sl:.2f} ({_fmt_pct(pct_sl)})")
    else:
        lines.append("📉 Sell Levels:")
        # Sell Below
        sb_line = f"Sell Below: {lv.sell_below:.2f}"
        lines.append(sb_line)
        # Targets (short side)
        for i, tgt in enumerate(lv.st, start=1):
            pct = (tgt - current_price) / current_price * 100.0
            lines.append(
                f"Target {i}: {tgt:.2f} ({_fmt_pct(pct)})"
            )
        sl = lv.sell_sl
        pct_sl = (sl - current_price) / current_price * 100.0
        lines.append(f"Stop Loss: {sl:.2f} ({_fmt_pct(pct_sl)})")
    return lines


def build_simple_alert(title: str, symbol: str, status_line: str, levels: 'Levels', current_price: Optional[float] = None, hit_level: Optional[str] = None, quantity: Optional[int] = None) -> str:
    # Determine current price fallback if not provided
    cp = current_price
    if cp is None:
        cp = get_live_price(symbol) or levels.previous_close
    # Header
    ts = now_ist().strftime("%Y-%m-%d %H:%M:%S IST%z")
    # Change vs previous close
    change_pct = ((cp - levels.previous_close) / levels.previous_close * 100.0) if levels.previous_close else 0.0
    # Status and side
    side = _detect_side_from_status(status_line) or ("BUY" if cp >= levels.buy_above else ("SELL" if cp <= levels.sell_below else "BUY"))
    lines: List[str] = []
    lines.append(f"🚨 {symbol} Alert at {ts}")
    lines.append("")
    lines.append(f"Previous Close: {levels.previous_close:.2f}")
    lines.append(f"Current Price: {cp:.2f}")
    lines.append(f"Change: {_fmt_pct(change_pct)}")
    lines.append(f"Deviation (X): {levels.x:.2f}")
    if quantity is not None:
        lines.append(f"Quantity: {quantity}")
    lines.append(f"Status: {status_line}")
    lines.append("")
    lines.append("")
    lines.append("📊 Technical Analysis:")
    lines.extend(_build_levels_section(side, levels, cp, hit_level))
    return "\n".join(lines)


def fmt_levels_table(symbol: str, levels: Levels) -> str:
    # Deprecated in favor of the rich alert format, kept for backward compatibility if needed
    lines = [f"{symbol}", f"PC: {levels.previous_close:.2f}  X: {levels.x:.2f}"]
    lines.append(
        "Buy: BA={:.2f} T1={:.2f} T2={:.2f} T3={:.2f} T4={:.2f} T5={:.2f} | SL={:.2f}".format(
            levels.buy_above, levels.t[0], levels.t[1], levels.t[2], levels.t[3], levels.t[4], levels.buy_sl
        )
    )
    lines.append(
        "Sell: SB={:.2f} ST1={:.2f} ST2={:.2f} ST3={:.2f} ST4={:.2f} ST5={:.2f} | SL={:.2f}".format(
            levels.sell_below, levels.st[0], levels.st[1], levels.st[2], levels.st[3], levels.st[4], levels.sell_sl
        )
    )
    return "\n".join(lines)


# ----------------------------
# Plotly Dash dashboard (optional)
# ----------------------------

def _empty_figure(message: str, height: int):
    fig = go.Figure()
    fig.add_annotation(
        text=message,
        xref="paper", yref="paper",
        x=0.5, y=0.5, showarrow=False,
        font=dict(size=14, color="#666"),
        align="center",
        bgcolor="rgba(255,255,255,0.7)",
    )
    fig.update_layout(margin=dict(l=40, r=10, t=20, b=20), height=height)
    fig.update_xaxes(visible=False)
    fig.update_yaxes(visible=False)
    return fig


def _add_level_lines(fig: 'go.Figure', lv: Levels, x_start: datetime, x_end: datetime) -> None:
    levels = [
        (lv.buy_above, "Buy Above", "#2e7d32"),
        (lv.t[0], "T1", "#2e7d32"),
        (lv.t[1], "T2", "#2e7d32"),
        (lv.t[2], "T3", "#2e7d32"),
        (lv.t[3], "T4", "#2e7d32"),
        (lv.t[4], "T5", "#2e7d32"),
        (lv.buy_sl, "Buy SL", "#1b5e20"),
        (lv.sell_below, "Sell Below", "#c62828"),
        (lv.st[0], "ST1", "#c62828"),
        (lv.st[1], "ST2", "#c62828"),
        (lv.st[2], "ST3", "#c62828"),
        (lv.st[3], "ST4", "#c62828"),
        (lv.st[4], "ST5", "#c62828"),
        (lv.sell_sl, "Sell SL", "#6a1b9a"),
    ]
    for y, name, color in levels:
        try:
            fig.add_shape(type="line", x0=x_start, x1=x_end, y0=y, y1=y, xref="x", yref="y", line=dict(color=color, width=1, dash="dash"))
            fig.add_annotation(x=x_end, y=y, text=f"{name} {y:.2f}", showarrow=False, xanchor="left", yanchor="middle", bgcolor="rgba(255,255,255,0.6)", font=dict(size=11, color=color))
        except Exception:
            pass


def _apply_indicator(fig: 'go.Figure', ohlc: pd.DataFrame, indicator: str) -> None:
    try:
        if indicator == "sma20":
            sma = ohlc["Close"].rolling(20, min_periods=1).mean()
            fig.add_trace(go.Scatter(x=ohlc.index, y=sma, name="SMA20", line=dict(color="#ff9800", width=1.5)))
        elif indicator == "ema20":
            ema = ohlc["Close"].ewm(span=20, adjust=False).mean()
            fig.add_trace(go.Scatter(x=ohlc.index, y=ema, name="EMA20", line=dict(color="#9c27b0", width=1.5)))
        elif indicator == "bbands":
            ma = ohlc["Close"].rolling(20, min_periods=1).mean()
            std = ohlc["Close"].rolling(20, min_periods=1).std(ddof=0)
            upper = ma + 2 * std
            lower = ma - 2 * std
            fig.add_trace(go.Scatter(x=ohlc.index, y=upper, name="BB Upper", line=dict(color="#3f51b5", width=1)))
            fig.add_trace(go.Scatter(x=ohlc.index, y=ma, name="BB MA", line=dict(color="#607d8b", width=1)))
            fig.add_trace(go.Scatter(x=ohlc.index, y=lower, name="BB Lower", line=dict(color="#3f51b5", width=1)))
        elif indicator == "vwap":
            # session VWAP from 09:15
            start = now_ist().replace(hour=9, minute=15, second=0, microsecond=0)
            df = ohlc.loc[ohlc.index >= start]
            typical = (df["High"] + df["Low"] + df["Close"]) / 3.0
            vol = df.get("Volume") if "Volume" in df.columns else pd.Series([1.0] * len(df), index=df.index)
            cum_vol_price = (typical * vol).cumsum()
            cum_vol = vol.cumsum().replace(0, pd.NA)
            vwap = (cum_vol_price / cum_vol).ffill()
            fig.add_trace(go.Scatter(x=df.index, y=vwap, name="VWAP", line=dict(color="#009688", width=1.5)))
    except Exception:
        pass


def build_symbol_figure(symbol: str, st: 'SymbolState', ohlc: Optional[pd.DataFrame], chart_height: int, indicator: str = "none"):
    # Fallback to locally cached price history if yfinance data is unavailable.
    if (ohlc is None or ohlc.empty) and PRICE_HISTORY.get(symbol):
        try:
            hist = get_price_history(symbol)
            if hist:
                hist_df = pd.DataFrame(hist, columns=["timestamp", "Close"]).set_index("timestamp")
                ohlc = hist_df
        except Exception as exc:
            logger.debug("Failed to build fallback history for %s: %s", symbol, exc)

    if ohlc is None or ohlc.empty:
        return _empty_figure("No data available for current Interval/Window.", chart_height)

    fig = go.Figure()
    try:
        fig.add_trace(
            go.Scatter(
                x=ohlc.index,
                y=ohlc["Close"].astype(float),
                mode="lines",
                name="Close",
                hovertemplate="%{x|%Y-%m-%d %H:%M:%S}<br>Close=%{y:.2f}<extra></extra>",
            )
        )
        _apply_indicator(fig, ohlc, indicator)
        # Level lines across current visible data
        _add_level_lines(fig, st.levels, ohlc.index[0], ohlc.index[-1])
    except Exception as e:
        return _empty_figure(f"Render error: {str(e)}", chart_height)

    lv = st.levels
    # Note: temporarily remove horizontal level lines to ensure charts render reliably.
    # We will add them back using simple shape lines after confirming candles display.

    # Current price marker
    if st.last_price is not None and ohlc is not None and not ohlc.empty:
        fig.add_trace(
            go.Scatter(x=[ohlc.index[-1]], y=[st.last_price], mode="markers", name="Last", marker=dict(color="orange", size=8))
        )

    fig.update_layout(
        title=f"{symbol} Live",
        margin=dict(l=40, r=10, t=40, b=30),
        legend=dict(orientation="h", yanchor="bottom", y=1.02, xanchor="right", x=1),
        height=chart_height,
        hovermode="x unified",
        uirevision=f"{symbol}_rev",  # preserve zoom/pan across updates
    )
    fig.update_xaxes(
        showspikes=True,
        spikemode="across",
        spikesnap="cursor",
        rangeslider=dict(visible=True),
        rangeselector=dict(
            buttons=[
                dict(count=15, label="15m", step="minute", stepmode="backward"),
                dict(count=30, label="30m", step="minute", stepmode="backward"),
                dict(count=1, label="1h", step="hour", stepmode="backward"),
                dict(step="all"),
            ]
        ),
    )
    fig.update_yaxes(showspikes=True, spikethickness=1)
    return fig


def start_dash_app(states: Dict[str, 'SymbolState']) -> None:
    if not ENABLE_DASH or not DASH_AVAILABLE:
        return

    app = Dash(__name__)
    default_syms = STOCKS[:]  # ALL stocks by default
    default_interval = "1m"
    default_window = "Today"
    # full-width charts only; no per-row control

    app.layout = html.Div([
        html.Div([
            html.H3("Live Levels Dashboard", style={"margin": "0 0 8px 0"}),
            html.Div([
                html.Button("Symbols", id="open_symbols", n_clicks=0, style={"height": "36px"}),
                html.Div("Interval", style={"marginLeft": "16px"}),
                dcc.Dropdown(
                    id="interval",
                    options=[{"label": iv, "value": iv} for iv in VALID_INTERVALS],
                    value=default_interval,
                    clearable=False,
                    style={"width": "110px"},
                ),
                html.Div("Window", style={"marginLeft": "16px"}),
                dcc.Dropdown(
                    id="window",
                    options=[{"label": w, "value": w} for w in ["Today", "6h", "1d"]],
                    value=default_window,
                    clearable=False,
                    style={"width": "110px"},
                ),
                html.Div("Indicator", style={"marginLeft": "16px"}),
                dcc.Dropdown(
                    id="indicator",
                    options=INDICATOR_OPTIONS,
                    value="none",
                    clearable=False,
                    style={"width": "180px"},
                ),
                dcc.Interval(id="tick", interval=2000, n_intervals=0),
            ], style={"display": "flex", "gap": "16px", "alignItems": "center", "flexWrap": "wrap"}),
            html.Div(id="alerts_panel", style={"marginTop": "8px", "fontSize": "13px", "maxHeight": "160px", "overflowY": "auto", "borderTop": "1px solid #eee", "paddingTop": "6px"}),
        ], style={"position": "sticky", "top": 0, "background": "#fafafa", "zIndex": 1, "padding": "8px 12px", "borderBottom": "1px solid #eee"}),
        # Modal overlay for symbols selection
        html.Div(id="symbols_modal", children=[
            html.Div([
                html.Div("Select Symbols", style={"fontWeight": "600", "marginBottom": "8px"}),
                dcc.Dropdown(
                    id="symbols",
                    options=[{"label": s, "value": s} for s in STOCKS],
                    value=default_syms,
                    multi=True,
                    persistence=True,
                    persistence_type="session",
                    style={"width": "100%"},
                ),
                html.Div([
                    html.Button("Select All", id="symbols_select_all", n_clicks=0),
                    html.Button("Deselect All", id="symbols_clear_all", n_clicks=0, style={"marginLeft": "8px"}),
                    html.Button("Close", id="symbols_close", n_clicks=0, style={"marginLeft": "8px"}),
                ], style={"marginTop": "10px"}),
            ], style={"background": "#fff", "padding": "12px", "borderRadius": "8px", "width": "520px", "maxWidth": "90%"}),
        ], style={"position": "fixed", "inset": 0, "display": "none", "alignItems": "center", "justifyContent": "center", "background": "rgba(0,0,0,0.35)", "zIndex": 1000}),
        html.Div(id="charts")
    ], style={"padding": "12px", "background": "#fff"})

    @app.callback(
        Output("symbols_modal", "style"),
        [Input("open_symbols", "n_clicks"), Input("symbols_close", "n_clicks")],
        prevent_initial_call=True,
    )
    def _toggle_symbols_modal(open_clicks, close_clicks):
        ctx = dash.callback_context
        if not ctx.triggered:
            raise dash.exceptions.PreventUpdate
        trig = ctx.triggered[0]["prop_id"].split(".")[0]
        show = trig == "open_symbols"
        return {"position": "fixed", "inset": 0, "display": ("flex" if show else "none"), "alignItems": "center", "justifyContent": "center", "background": "rgba(0,0,0,0.35)", "zIndex": 1000}

    @app.callback(
        Output("symbols", "value"),
        [Input("symbols_select_all", "n_clicks"), Input("symbols_clear_all", "n_clicks")],
        State("symbols", "value"),
        prevent_initial_call=True,
    )
    def _symbols_select_clear(n_all, n_clear, current):
        ctx = dash.callback_context
        if not ctx.triggered:
            raise dash.exceptions.PreventUpdate
        trig = ctx.triggered[0]["prop_id"].split(".")[0]
        if trig == "symbols_select_all":
            return STOCKS
        if trig == "symbols_clear_all":
            return []
        raise dash.exceptions.PreventUpdate

    @app.callback(
        [Output("charts", "children"), Output("alerts_panel", "children")],
        [
            Input("symbols", "value"),
            Input("interval", "value"),
            Input("window", "value"),
            Input("indicator", "value"),
            Input("tick", "n_intervals"),
        ],
    )
    def _render(selected: List[str], interval: str, window: str, indicator: str, _n: int):
        children = []
        # Check market status
        now_local = now_ist()
        is_market_open = market_open(now_local)
        show_eod_analysis = (now_local.hour == 15 and now_local.minute >= 30) or now_local.hour > 15
        
        # Show EOD Analysis section if after 15:30
        if show_eod_analysis:
            try:
                analysis = calculate_eod_analysis()
                gl = analysis['global']
                
                # Global summary
                eod_section = html.Div([
                    html.H3("📊 EOD Analysis", style={"marginTop": "20px", "marginBottom": "10px", "color": "#333"}),
                    html.Div([
                        html.Div([
                            html.Strong("Total Realized P&L: "), f"₹{gl['total_realized']:.2f}",
                        ], style={"marginBottom": "8px", "fontSize": "16px"}),
                        html.Div([
                            html.Strong("Total Unrealized P&L: "), f"₹{gl['total_unrealized']:.2f}",
                        ], style={"marginBottom": "8px", "fontSize": "16px"}),
                        html.Div([
                            html.Strong("Total Net P&L: "), 
                            html.Span(f"₹{gl['total_net']:.2f}", style={"color": "#2e7d32" if gl['total_net'] >= 0 else "#c62828", "fontWeight": "bold"}),
                        ], style={"marginBottom": "12px", "fontSize": "18px"}),
                        html.Div([
                            html.Strong("Win Rate: "), f"{gl['win_rate']:.1f}%",
                            html.Span(" | ", style={"margin": "0 8px"}),
                            html.Strong("BUY Win Rate: "), f"{gl['buy_win_rate']:.1f}%",
                            html.Span(" | ", style={"margin": "0 8px"}),
                            html.Strong("SELL Win Rate: "), f"{gl['sell_win_rate']:.1f}%",
                        ], style={"marginBottom": "12px", "fontSize": "14px", "color": "#555"}),
                        html.Div([
                            html.Strong("BUY Realized: "), f"₹{gl['buy_realized']:.2f}",
                            html.Span(" | ", style={"margin": "0 8px"}),
                            html.Strong("SELL Realized: "), f"₹{gl['sell_realized']:.2f}",
                        ], style={"marginBottom": "8px", "fontSize": "14px"}),
                        html.Div([
                            html.Strong("Target Distribution: "),
                            f"T1:{gl['target_counts']['T1']} T2:{gl['target_counts']['T2']} T3:{gl['target_counts']['T3']} T4:{gl['target_counts']['T4']} T5:{gl['target_counts']['T5']} | ",
                            f"ST1:{gl['target_counts']['ST1']} ST2:{gl['target_counts']['ST2']} ST3:{gl['target_counts']['ST3']} ST4:{gl['target_counts']['ST4']} ST5:{gl['target_counts']['ST5']}",
                        ], style={"marginBottom": "8px", "fontSize": "14px"}),
                        html.Div([
                            html.Strong("Stop Loss: "), f"BUY_SL:{gl['sl_counts']['BUY_SL']} SELL_SL:{gl['sl_counts']['SELL_SL']}",
                        ], style={"marginBottom": "12px", "fontSize": "14px"}),
                    ], style={"background": "#f5f5f5", "padding": "12px", "borderRadius": "6px", "marginBottom": "16px"}),
                    
                    # Per-symbol table
                    html.Div([
                        html.H4("Per-Symbol Breakdown", style={"marginBottom": "8px", "fontSize": "16px"}),
                        html.Table([
                            html.Thead([
                                html.Tr([
                                    html.Th("Symbol", style={"padding": "8px", "textAlign": "left", "background": "#f0f0f0", "border": "1px solid #ddd"}),
                                    html.Th("Realized", style={"padding": "8px", "textAlign": "right", "background": "#f0f0f0", "border": "1px solid #ddd"}),
                                    html.Th("Unrealized", style={"padding": "8px", "textAlign": "right", "background": "#f0f0f0", "border": "1px solid #ddd"}),
                                    html.Th("Total", style={"padding": "8px", "textAlign": "right", "background": "#f0f0f0", "border": "1px solid #ddd"}),
                                    html.Th("BUY Hits", style={"padding": "8px", "textAlign": "center", "background": "#f0f0f0", "border": "1px solid #ddd"}),
                                    html.Th("SELL Hits", style={"padding": "8px", "textAlign": "center", "background": "#f0f0f0", "border": "1px solid #ddd"}),
                                ])
                            ]),
                            html.Tbody([
                                html.Tr([
                                    html.Td(sym, style={"padding": "6px", "border": "1px solid #ddd"}),
                                    html.Td(f"₹{data['realized']:.2f}", style={"padding": "6px", "textAlign": "right", "border": "1px solid #ddd"}),
                                    html.Td(f"₹{data['unrealized']:.2f}", style={"padding": "6px", "textAlign": "right", "border": "1px solid #ddd"}),
                                    html.Td(
                                        f"₹{data['total']:.2f}", 
                                        style={
                                            "padding": "6px", 
                                            "textAlign": "right",
                                            "color": "#2e7d32" if data['total'] >= 0 else "#c62828",
                                            "fontWeight": "bold",
                                            "border": "1px solid #ddd"
                                        }
                                    ),
                                    html.Td(
                                        f"T1:{data['buy_hits']['T1']} T2:{data['buy_hits']['T2']} T3:{data['buy_hits']['T3']} T4:{data['buy_hits']['T4']} T5:{data['buy_hits']['T5']} SL:{data['buy_hits']['SL']}",
                                        style={"padding": "6px", "textAlign": "center", "fontSize": "12px", "border": "1px solid #ddd"}
                                    ),
                                    html.Td(
                                        f"ST1:{data['sell_hits']['ST1']} ST2:{data['sell_hits']['ST2']} ST3:{data['sell_hits']['ST3']} ST4:{data['sell_hits']['ST4']} ST5:{data['sell_hits']['ST5']} SL:{data['sell_hits']['SL']}",
                                        style={"padding": "6px", "textAlign": "center", "fontSize": "12px", "border": "1px solid #ddd"}
                                    ),
                                ])
                                for sym, data in sorted(analysis['symbols'].items(), key=lambda x: x[1]['total'], reverse=True)
                                if data['realized'] != 0 or data['unrealized'] != 0
                            ])
                        ], style={"width": "100%", "borderCollapse": "collapse", "fontSize": "13px", "border": "1px solid #ddd"})
                    ], style={"marginTop": "16px"}),
                ], style={"background": "#fff", "padding": "16px", "borderRadius": "8px", "border": "2px solid #4caf50", "marginBottom": "20px"})
                children.append(eod_section)
            except Exception as e:
                logger.debug(f"EOD analysis error: {e}")
        
        # If market is closed, show message
        if not is_market_open:
            next_open = now_local.replace(hour=9, minute=15, second=0, microsecond=0)
            if now_local.hour >= 15 or (now_local.hour == 15 and now_local.minute >= 30):
                # Market closed for today, show next day
                next_open = next_open + timedelta(days=1)
            
            message = html.Div([
                html.H2("Market is Closed", style={"textAlign": "center", "color": "#666", "marginTop": "100px"}),
                html.P(f"Next trading session starts at {next_open.strftime('%H:%M IST')} on {next_open.strftime('%Y-%m-%d')}", 
                       style={"textAlign": "center", "color": "#999", "fontSize": "18px"}),
                html.P(f"Current time: {now_local.strftime('%Y-%m-%d %H:%M:%S IST')}", 
                       style={"textAlign": "center", "color": "#999", "fontSize": "14px", "marginTop": "20px"}),
            ], style={"width": "100%", "minHeight": "400px"})
            children.append(message)
        else:
            # Market is open, render charts
            # Robust defaults if dropdown value not propagated yet
            if not selected:
                selected = default_syms
            if not interval:
                interval = "1m"
            if not window:
                window = "Today"
            if not indicator:
                indicator = "none"
            chart_height = 520
            row: List[html.Div] = []
            for idx, sym in enumerate(selected):
                try:
                    st = states.get(sym)
                    if not st:
                        continue
                    ohlc = fetch_intraday_ohlc(sym, interval, window)
                    fig = build_symbol_figure(sym, st, ohlc, chart_height, indicator)
                    card_body = dcc.Graph(
                        figure=fig,
                        config={
                            "displayModeBar": True,
                            "scrollZoom": True,
                            "doubleClick": "reset",
                            "responsive": True,
                            "modeBarButtonsToAdd": [
                                "drawline",
                                "drawopenpath",
                                "drawrect",
                                "drawcircle",
                                "eraseshape",
                            ],
                        },
                    )
                    # Realized events panel under chart
                    events_view = []
                    try:
                        with EVENTS_LOCK:
                            events = list(REALIZED_EVENTS.get(sym, []))
                        if events:
                            for ev in events[::-1]:  # latest first
                                events_view.append(html.Div(
                                    f"{ev['time']} {ev['event']} {ev['side']} qty {ev['qty']} @ {ev['price']:.2f} | Gross {ev['gross']:.2f} | Net {ev['net']:.2f}",
                                    style={"fontSize": "12px", "color": "#444"}
                                ))
                        else:
                            events_view.append(html.Div("No realized P&L yet", style={"fontSize": "12px", "color": "#888"}))
                    except Exception:
                        events_view = []

                    card = html.Div([
                        html.Div(sym, style={"fontWeight": "600", "marginBottom": "4px"}),
                        dcc.Loading(type="dot", children=card_body),
                        html.Div(events_view, style={"marginTop": "6px", "borderTop": "1px dashed #eee", "paddingTop": "6px"}),
                    ], style={"border": "1px solid #eaeaea", "padding": "8px", "borderRadius": "8px", "marginBottom": "12px", "width": "100%", "boxShadow": "0 1px 2px rgba(0,0,0,0.04)"})
                    row.append(card)
                except Exception as e:
                    err_fig = _empty_figure(f"Error: {str(e)}", chart_height)
                    card_body = dcc.Graph(figure=err_fig, config={"displayModeBar": False})
                    events_view = []
                    card = html.Div([
                        html.Div(sym, style={"fontWeight": "600", "marginBottom": "4px"}),
                        dcc.Loading(type="dot", children=card_body),
                        html.Div(events_view, style={"marginTop": "6px", "borderTop": "1px dashed #eee", "paddingTop": "6px"}),
                    ], style={"border": "1px solid #eaeaea", "padding": "8px", "borderRadius": "8px", "marginBottom": "12px", "width": "100%", "boxShadow": "0 1px 2px rgba(0,0,0,0.04)"})
                    row.append(card)
            if row:
                children.extend(row)
            else:
                # No symbols selected
                children.append(html.Div([
                    html.P("No symbols selected. Click 'Symbols' button to select stocks.", 
                           style={"textAlign": "center", "color": "#999", "fontSize": "16px", "marginTop": "100px"})
                ]))

        # build alerts list
        try:
            alerts = get_recent_alerts(limit=15)
            alert_children = []
            for ts, txt in alerts[::-1]:
                alert_children.append(html.Div([
                    html.Span(ts.strftime('%H:%M:%S'), style={"color": "#666", "marginRight": "6px"}),
                    html.Span(html.Span(txt.replace('\n', ' | ')))
                ]))
        except Exception:
            alert_children = []

        return children, alert_children

    def _run():
        try:
            # Dash 3+: use app.run instead of deprecated run_server
            # Host 0.0.0.0 allows access from any IP address
            logger.info(f"Starting dashboard on http://0.0.0.0:{DASH_PORT}")
            app.run(host="0.0.0.0", port=DASH_PORT, debug=False)
        except Exception as e:
            logger.error(f"Dashboard startup failed: {e}")

    th = threading.Thread(target=_run, daemon=True)
    th.start()
    # Optionally expose publicly
    public_url = start_public_tunnel(DASH_PORT)
    if public_url:
        logger.info(f"Public dashboard URL: {public_url}")
        try:
            send_telegram(f"Dashboard public URL: {public_url}")
        except Exception:
            pass
    elif ENABLE_TUNNEL:
        try:
            send_telegram("Dashboard public URL unavailable: ensure Cloudflare (cloudflared) or pyngrok is installed and configured")
        except Exception:
            pass


# ----------------------------
# Premarket replay (startup)
# ----------------------------

def fetch_premarket_history_1m(symbol: str) -> Optional[pd.DataFrame]:
    """Fetch today's 1m data and return rows between 09:15–09:30 IST.

    Returns a DataFrame with at least the Close column, index localized to IST.
    """
    try:
        t = yf.Ticker(f"{symbol}.NS")
        df = t.history(period="1d", interval="1m")
        if df is None or df.empty:
            return None
        # Ensure tz-aware in IST
        if df.index.tz is None:
            df.index = df.index.tz_localize(pytz.UTC).tz_convert(IST)
        else:
            df.index = df.index.tz_convert(IST)
        start_ts = now_ist().replace(hour=9, minute=15, second=0, microsecond=0)
        end_ts = now_ist().replace(hour=9, minute=30, second=0, microsecond=0)
        mask = (df.index >= start_ts) & (df.index <= end_ts)
        sub = df.loc[mask]
        return sub if not sub.empty else None
    except Exception as e:
        logger.debug(f"premarket history error {symbol}: {e}")
        return None


def replay_premarket_adjustments(state: SymbolState) -> None:
    """If started after 09:30, replay 1m closes between 09:15–09:30 and adjust levels.

    Alerts:
    - If no premarket data found: alert.
    - If falling back to current price due to missing data: alert before fallback.
    - If levels updated (via replay or fallback): alert with updated table.
    """
    symbol = state.symbol
    lv = state.levels
    hist = fetch_premarket_history_1m(symbol)
    send_ok = market_open(now_ist())  # send alerts only during 09:15–15:30

    if hist is None:
        # No premarket data; keep initial levels and inform (no fallback adjustment)
        if send_ok:
            base_lv = state.initial_levels or lv
            msg = build_simple_alert(
                "Premarket Replay", symbol,
                "No premarket data found for 09:15–09:30. Using initial levels (no adjustment).",
                base_lv,
                current_price=state.last_price or base_lv.previous_close,
                quantity=(state.qty_remaining if state.in_position else None)
            )
            send_telegram(msg)
        return

    # Iterate minute closes in chronological order; use adjust_levels_premarket to simulate shifts
    adjusted_any = False
    for ts, row in hist.iterrows():
        close_px = float(row.get("Close", float("nan")))
        if math.isnan(close_px):
            continue
        new_levels, crossed, _side = adjust_levels_premarket(state.levels, close_px)
        if crossed is not None:
            old_lv = state.levels
            state.levels = new_levels
            adjusted_any = True
            if send_ok:
                compare_msg = build_premarket_adjustment_comparison_alert(
                    symbol, state.initial_levels or old_lv, state.levels, close_px,
                    f"crossed {crossed} at {close_px:.2f}"
                )
                send_telegram(compare_msg)

    # If consolidated messaging is desired, it can be added here; kept silent to avoid duplicates


# ----------------------------
# Core monitoring
# ----------------------------

def build_table(states: Dict[str, SymbolState]) -> Table:
    table = Table(title="Live NSE Levels", show_lines=False)
    table.add_column("Symbol", justify="left")
    table.add_column("Price", justify="right")
    table.add_column("BuyAbove", justify="right")
    table.add_column("T1", justify="right")
    table.add_column("T2", justify="right")
    table.add_column("T3", justify="right")
    table.add_column("T4", justify="right")
    table.add_column("T5", justify="right")
    table.add_column("Buy SL", justify="right")
    table.add_column("SellBelow", justify="right")
    table.add_column("ST1", justify="right")
    table.add_column("ST2", justify="right")
    table.add_column("ST3", justify="right")
    table.add_column("ST4", justify="right")
    table.add_column("ST5", justify="right")
    table.add_column("Sell SL", justify="right")
    table.add_column("Pos", justify="left")

    for sym, st in states.items():
        lv = st.levels
        pos = "-"
        if st.in_position and st.side:
            pos = f"{st.side} {st.qty_remaining}"  # show remaining qty
        table.add_row(
            sym,
            f"{(st.last_price or 0):.2f}",
            f"{lv.buy_above:.2f}",
            f"{lv.t[0]:.2f}", f"{lv.t[1]:.2f}", f"{lv.t[2]:.2f}", f"{lv.t[3]:.2f}", f"{lv.t[4]:.2f}",
            f"{lv.buy_sl:.2f}",
            f"{lv.sell_below:.2f}",
            f"{lv.st[0]:.2f}", f"{lv.st[1]:.2f}", f"{lv.st[2]:.2f}", f"{lv.st[3]:.2f}", f"{lv.st[4]:.2f}",
            f"{lv.sell_sl:.2f}",
            pos,
        )
    return table


def maybe_alert_once(state: SymbolState, key: str, text: str) -> None:
    if key in state.sent_events:
        return
    now_local = now_ist()
    # Between 09:15–09:30, only allow premarket level adjustment alerts.
    # Identify them by key prefix or message title text.
    if premarket_window(now_local):
        is_premarket_adjust = key.startswith("premkt_adjust_") or ("Premarket" in text and "Adjustment" in text)
        if not is_premarket_adjust:
            return
    if alerts_allowed(now_local):
        send_telegram(text)
        state.sent_events.add(key)


def handle_premarket_adjustment(state: SymbolState, price: float) -> None:
    before = state.levels
    adjusted, crossed, _ = adjust_levels_premarket(before, price)
    if crossed is not None and not state.adjusted_locked:
        state.levels = adjusted
        msg = build_premarket_adjustment_comparison_alert(
            state.symbol,
            state.initial_levels or before,
            state.levels,
            price,
            f"crossed {crossed} at {price:.2f}"
        )
        maybe_alert_once(state, f"premkt_adjust_{crossed}", msg)


def try_entry(state: SymbolState, price: float) -> None:
    if state.in_position:
        return
    lv = state.levels
    now = now_ist()
    # Prevent same-day re-entry after a full exit
    today_key = now.strftime("%Y%m%d")
    if state.trade_date != today_key:
        state.trade_date = today_key
        state.exited_today = False
    if state.exited_today:
        return
    if not alerts_allowed(now):
        return
    # No trading before 9:30 AM
    if now.hour < 9 or (now.hour == 9 and now.minute < 30):
        return
    # Entry rules
    if price >= lv.buy_above:
        state.in_position = True
        state.side = "BUY"
        state.entry_price = price
        state.entry_time = now
        # dynamic quantity sizing: floor(50000 / entry_price), min 1
        dyn_qty = max(1, int(50000 // price))
        state.qty_remaining = dyn_qty
        state.qty_total = dyn_qty
        state.buy_trailing_sl = lv.buy_sl
        # Flat brokerage at entry
        # (recorded at exit time for net PnL; entry event brokerage noted here if needed)
        msg = build_simple_alert("Entry", state.symbol, f"BUY TRIGGERED", lv, current_price=price, hit_level="BUY_ABOVE", quantity=dyn_qty)
        maybe_alert_once(state, f"entry_buy", msg)
        log_trade_event(now, state.symbol, 'BUY_ENTRY', price, 'BUY', dyn_qty)
    elif price <= lv.sell_below:
        state.in_position = True
        state.side = "SELL"
        state.entry_price = price
        state.entry_time = now
        dyn_qty = max(1, int(50000 // price))
        state.qty_remaining = dyn_qty
        state.qty_total = dyn_qty
        state.sell_trailing_sl = lv.sell_sl
        msg = build_simple_alert("Entry", state.symbol, f"SELL TRIGGERED", lv, current_price=price, hit_level="SELL_BELOW", quantity=dyn_qty)
        maybe_alert_once(state, f"entry_sell", msg)
        log_trade_event(now, state.symbol, 'SELL_ENTRY', price, 'SELL', dyn_qty)


def handle_targets_and_trailing(state: SymbolState, price: float, partial_exits: List[dict]) -> None:
    if not state.in_position or not state.side:
        return
    now = now_ist()
    # No trading before 9:30 AM
    if now.hour < 9 or (now.hour == 9 and now.minute < 30):
        return
    lv = state.levels
    x = lv.x

    if state.side == "BUY":
        # First target/level hit closes full qty
        for idx, tgt in enumerate(lv.t):
            if price >= tgt:
                qty_to_exit = state.qty_remaining
                gross_pl = lv.x * qty_to_exit
                net_pl = gross_pl - (BROKERAGE_FLAT_PER_SIDE + BROKERAGE_FLAT_PER_SIDE)  # entry + exit
                # record for dashboard
                record_realized_event(state.symbol, 'BUY', f'T{idx+1}', tgt, qty_to_exit, gross_pl, net_pl)
                msg = build_simple_alert(
                    "Exit",
                    state.symbol,
                    f"T{idx+1} HIT (exited {qty_to_exit}) | Gross {gross_pl:.2f} | Net {net_pl:.2f}",
                    state.levels,
                    current_price=tgt,
                    hit_level=f"T{idx+1}",
                    quantity=qty_to_exit,
                )
                maybe_alert_once(state, f"buy_t{idx+1}_full", msg)
                log_trade_event(now, state.symbol, f"T{idx+1}", tgt, 'BUY', qty_to_exit, entry_price=state.entry_price)
                # Close position
                state.in_position = False
                state.side = None
                state.qty_remaining = state.qty_total
                state.last_target_hit_index = -1
                state.entry_price = None
                state.entry_time = None
                state.buy_trailing_sl = None
                state.exited_today = True
                return
        # Stop loss check (full exit)
        if price <= (state.buy_trailing_sl or lv.buy_sl):
            qty_to_exit = state.qty_remaining
            gross_pl = -lv.x * qty_to_exit
            net_pl = gross_pl - (BROKERAGE_FLAT_PER_SIDE + BROKERAGE_FLAT_PER_SIDE)
            record_realized_event(state.symbol, 'BUY', 'BUY_SL', price, qty_to_exit, gross_pl, net_pl)
            msg = build_simple_alert("Exit", state.symbol, f"BUY STOP LOSS HIT | Gross {gross_pl:.2f} | Net {net_pl:.2f}", state.levels, current_price=price, hit_level="BUY_SL", quantity=qty_to_exit)
            maybe_alert_once(state, f"buy_sl_close_full", msg)
            log_trade_event(now, state.symbol, 'BUY_SL', price, 'BUY', qty_to_exit, entry_price=state.entry_price)
            state.in_position = False
            state.side = None
            state.qty_remaining = state.qty_total
            state.last_target_hit_index = -1
            state.entry_price = None
            state.entry_time = None
            state.buy_trailing_sl = None
            state.exited_today = True
    else:  # SELL
        for idx, tgt in enumerate(lv.st):
            if price <= tgt:
                qty_to_exit = state.qty_remaining
                gross_pl = lv.x * qty_to_exit
                net_pl = gross_pl - (BROKERAGE_FLAT_PER_SIDE + BROKERAGE_FLAT_PER_SIDE)
                # record for dashboard
                record_realized_event(state.symbol, 'SELL', f'ST{idx+1}', tgt, qty_to_exit, gross_pl, net_pl)
                msg = build_simple_alert(
                    "Exit",
                    state.symbol,
                    f"ST{idx+1} HIT (exited {qty_to_exit}) | Gross {gross_pl:.2f} | Net {net_pl:.2f}",
                    state.levels,
                    current_price=tgt,
                    hit_level=f"ST{idx+1}",
                    quantity=qty_to_exit,
                )
                maybe_alert_once(state, f"sell_st{idx+1}_full", msg)
                log_trade_event(now, state.symbol, f"ST{idx+1}", tgt, 'SELL', qty_to_exit, entry_price=state.entry_price)
                state.in_position = False
                state.side = None
                state.qty_remaining = state.qty_total
                state.last_target_hit_index = -1
                state.entry_price = None
                state.entry_time = None
                state.sell_trailing_sl = None
                state.exited_today = True
                return
        if price >= (state.sell_trailing_sl or lv.sell_sl):
            qty_to_exit = state.qty_remaining
            gross_pl = -lv.x * qty_to_exit
            net_pl = gross_pl - (BROKERAGE_FLAT_PER_SIDE + BROKERAGE_FLAT_PER_SIDE)
            record_realized_event(state.symbol, 'SELL', 'SELL_SL', price, qty_to_exit, gross_pl, net_pl)
            msg = build_simple_alert("Exit", state.symbol, f"SELL STOP LOSS HIT | Gross {gross_pl:.2f} | Net {net_pl:.2f}", state.levels, current_price=price, hit_level="SELL_SL", quantity=qty_to_exit)
            maybe_alert_once(state, f"sell_sl_close_full", msg)
            log_trade_event(now, state.symbol, 'SELL_SL', price, 'SELL', qty_to_exit, entry_price=state.entry_price)
            state.in_position = False
            state.side = None
            state.qty_remaining = state.qty_total
            state.last_target_hit_index = -1
            state.entry_price = None
            state.entry_time = None
            state.sell_trailing_sl = None
            state.exited_today = True


def eod_square_off(states: Dict[str, SymbolState], last_prices: Dict[str, float], partial_exits: List[dict], final_exits: List[dict]) -> None:
    for sym, st in states.items():
        if st.in_position and st.side and st.qty_remaining > 0:
            px = last_prices.get(sym) or st.last_price or 0.0
            qty = st.qty_remaining
            # Gross PnL per confirmed rules for open positions
            if st.side == "BUY":
                gross_pl = (px - (st.entry_price or px)) * qty
            else:
                gross_pl = ((st.entry_price or px) - px) * qty
            # Apply flat brokerage for both entry and exit (₹10 each side)
            brokerage = BROKERAGE_FLAT_PER_SIDE + BROKERAGE_FLAT_PER_SIDE
            net_pl = gross_pl - brokerage
            final_exits.append({
                "symbol": sym,
                "side": st.side,
                "qty": qty,
                "price": px,
                "net_profit": net_pl,
                "brokerage": brokerage,
                "time": now_ist().isoformat(),
                "exit_type": "EOD"
            })
            st.in_position = False
            st.side = None
            st.qty_remaining = st.qty_total
            st.last_target_hit_index = -1
            st.entry_price = None
            st.entry_time = None
            st.buy_trailing_sl = None
            st.sell_trailing_sl = None
            st.exited_today = True
            log_trade_event(now_ist(), sym, 'EOD_CLOSE', px, st.side, qty)


def send_eod_summary(partial_exits: List[dict], final_exits: List[dict]) -> None:
    total_profit = 0.0
    total_brokerage = 0.0
    ts = now_ist().strftime("%Y-%m-%d %H:%M:%S IST%z")
    lines: List[str] = [f"🚨 EOD Summary at {ts}"]
    if partial_exits:
        lines.append("\nPartial Exits:")
        for p in partial_exits:
            total_profit += p.get("profit", 0.0)
            lines.append(f"{p['symbol']} {p['side']} {p.get('target','')} qty {p['qty']} @ {p['price']:.2f} P/L {p['profit']:.2f}")
    if final_exits:
        lines.append("\nFinal Exits:")
        for f in final_exits:
            total_profit += f.get("net_profit", 0.0)
            total_brokerage += f.get("brokerage", 0.0)
            lines.append(f"{f['symbol']} {f['side']} qty {f['qty']} @ {f['price']:.2f} Net {f['net_profit']:.2f} (after {f['brokerage']:.2f}) {f['exit_type']}")
    lines.append(f"\nTotal Profit: {total_profit:.2f}")
    lines.append(f"Total Brokerage: {total_brokerage:.2f}")
    lines.append(f"Net Profit: {(total_profit - total_brokerage):.2f}")
    send_telegram("\n".join(lines))


def send_eod_open_positions_summary(states: Dict[str, 'SymbolState'], last_prices: Dict[str, float]) -> None:
    ts = now_ist().strftime("%Y-%m-%d %H:%M:%S IST%z")
    lines: List[str] = [f"🚨 EOD Open Positions Summary at {ts}", ""]
    any_open = False
    total_gross = 0.0
    total_net = 0.0
    for sym, st in states.items():
        if st.in_position and st.side and (st.qty_remaining or 0) > 0:
            any_open = True
            px = last_prices.get(sym) or st.last_price or (st.entry_price or 0.0)
            qty = st.qty_remaining
            if st.side == "BUY":
                gross_pl = (px - (st.entry_price or px)) * qty
            else:
                gross_pl = ((st.entry_price or px) - px) * qty
            brokerage = BROKERAGE_FLAT_PER_SIDE + BROKERAGE_FLAT_PER_SIDE
            net_pl = gross_pl - brokerage
            total_gross += gross_pl
            total_net += net_pl
            # record an EOD open P&L line for dashboard under chart
            record_realized_event(sym, st.side, 'EOD_OPEN', px, qty, gross_pl, net_pl)
            lines.append(
                f"{sym} {st.side} qty {qty} entry {(st.entry_price or 0):.2f} EOD {px:.2f} | Gross {gross_pl:.2f} Net {net_pl:.2f}"
            )
    if not any_open:
        lines.append("No open positions at EOD.")
    else:
        lines.append("")
        lines.append(f"Total Gross P&L: {total_gross:.2f}")
        lines.append(f"Total Net P&L (after brokerage): {total_net:.2f}")
    send_telegram("\n".join(lines))


# ----------------------------
# Main
# ----------------------------

def main():
    if not TELEGRAM_CHAT_ID:
        logger.warning("TELEGRAM_CHAT_ID not set. Set env TELEGRAM_CHAT_ID to enable alerts.")

    console = Console()

    # Initialize states with previous close and initial levels
    states: Dict[str, SymbolState] = {}
    for sym in STOCKS:
        pc = get_prev_close(sym)
        if pc is None:
            continue
        levels = calc_levels_for_symbol(sym, pc)
        states[sym] = SymbolState(symbol=sym, levels=levels, initial_levels=levels)

    # Initialize price history and start dashboard if enabled
    init_price_history(list(states.keys()))
    if ENABLE_DASH and DASH_AVAILABLE:
        start_dash_app(states)
        logger.info(f"Dash dashboard starting on http://0.0.0.0:{DASH_PORT}")
        logger.info(f"Access from this machine: http://localhost:{DASH_PORT}")
        logger.info(f"Access from other devices: http://[YOUR_IP]:{DASH_PORT}")
    elif ENABLE_DASH and not DASH_AVAILABLE:
        logger.warning("Dashboard enabled but Dash dependencies not available. Install with: pip install dash plotly")

    # Export initial levels to an Excel sheet at program start
    try:
        rows = []
        for sym, st in states.items():
            lv = st.levels
            rows.append({
                "symbol": sym,
                "previous_close": lv.previous_close,
                "x": lv.x,
                "buy_above": lv.buy_above,
                "t1": lv.t[0],
                "t2": lv.t[1],
                "t3": lv.t[2],
                "t4": lv.t[3],
                "t5": lv.t[4],
                "buy_sl": lv.buy_sl,
                "sell_below": lv.sell_below,
                "st1": lv.st[0],
                "st2": lv.st[1],
                "st3": lv.st[2],
                "st4": lv.st[3],
                "st5": lv.st[4],
                "sell_sl": lv.sell_sl,
            })
        if rows:
            df = pd.DataFrame(rows)
            levels_dir = "levels"
            os.makedirs(levels_dir, exist_ok=True)
            out_name = os.path.join(levels_dir, f"initial_levels_{now_ist().strftime('%Y%m%d_%H%M%S')}.xlsx")
            df.to_excel(out_name, index=False)
            logger.info(f"Initial levels exported to {out_name}")
    except Exception as e:
        logger.warning(f"Failed to export initial levels Excel: {e}")

    partial_exits: List[dict] = []
    final_exits: List[dict] = []

    # If program starts anytime on/after 09:30, first replay premarket once
    now = now_ist()
    start_930 = now.replace(hour=9, minute=30, second=0, microsecond=0)
    end_1530 = now.replace(hour=15, minute=30, second=0, microsecond=0)
    if now >= start_930 and now <= end_1530:
        for sym, st in states.items():
            replay_premarket_adjustments(st)
            st.adjusted_locked = True  # lock further adjustments after replay
    else:
        # Outside market hours: do not run premarket replay or any adjustments
        for sym, st in states.items():
            st.adjusted_locked = True

    # Main loop (keep running even after 15:30 to keep dashboard live)
    cur_interval_idx = 0
    eod_sent = False
    with Live(build_table(states), console=console, refresh_per_second=8) as live:
        while True:
            now = now_ist()
            # EOD summary once at/after 15:30; keep program running for dashboard
            if (now.hour == 15 and now.minute >= 30) and not eod_sent:
                last_prices = {s: (states[s].last_price or 0.0) for s in states}
                # Send ONLY open positions summary (no closed trades here)
                send_eod_open_positions_summary(states, last_prices)
                # Then square off any remaining open positions for accounting
                eod_square_off(states, last_prices, partial_exits, final_exits)
                # Do not send the old summary
                eod_sent = True

            # Fetch and process per symbol
            for sym, st in states.items():
                price = get_live_price(sym)
                # During 09:15–09:30, yfinance fast_info can be stale/None.
                # Fallback to the latest 1m Close so premarket adjustments and alerts still occur.
                if price is None and premarket_window(now):
                    try:
                        df_fallback = fetch_intraday_ohlc(sym, "1m", "Today")
                        if df_fallback is not None and not df_fallback.empty:
                            price = float(df_fallback["Close"].astype(float).iloc[-1])
                    except Exception:
                        price = None
                if price is None:
                    continue
                st.last_price = price
                append_price_history(sym, now, price)

                # Premarket adjustment only within 9:15-9:30
                if premarket_window(now):
                    st.adjusted_locked = False
                    handle_premarket_adjustment(st, price)
                else:
                    st.adjusted_locked = True  # lock adjustments after 9:30

                # Entries and monitoring only during market hours (after 9:30)
                if market_open(now) and not premarket_window(now):
                    try_entry(st, price)
                    handle_targets_and_trailing(st, price, partial_exits)

            # Update live table
            live.update(build_table(states))

            # Pace control with fallback intervals
            sleep_s = UPDATE_INTERVALS_SECONDS[cur_interval_idx]
            try:
                time.sleep(sleep_s)
            except Exception:
                pass

    console.print("Done. EOD summary sent.")
    eod_save_summary_excel(TRADE_LOG, states, last_prices, date_str)


def compute_eod_pnl_from_alerts(alert_feed, last_prices):
    import re
    from collections import defaultdict
    positions = defaultdict(list) # symbol -> list of [entry dicts]
    # Basic regexps for parsing needed fields
    entry_pat = re.compile(r"(BUY|SELL) TRIGGERED", re.I)
    exit_pat = re.compile(r"(T\d|ST\d|STOP LOSS HIT)", re.I)
    qty_pat = re.compile(r"Quantity: (\d+)")
    price_pat = re.compile(r"Current Price: ([\d.]+)")
    sym_pat = re.compile(r"^🚨 ([A-Z0-9]+)\b")
    side_pat = re.compile(r"BUY|SELL", re.I)
    t1_pat = re.compile(r"Status: (T\d|ST\d|STOP LOS[SS] HIT|BUY TRIGGERED|SELL TRIGGERED)")
    entry_px_pat = re.compile(r"Entry Price: ([\d.]+)")
    # Logged results
    realized_pl = 0
    total_brokerage = 0
    open_positions = {}
    alert_seen = set()
    for ts, txt in alert_feed:
        if txt in alert_seen: continue
        alert_seen.add(txt)
        # Symbol
        m = sym_pat.search(txt)
        if not m: continue
        symbol = m.group(1)
        # Side
        mside = entry_pat.search(txt) or side_pat.search(txt)
        side = mside.group(1).upper() if mside else None
        # Entry: BUY/SELL TRIGGERED
        if entry_pat.search(txt):
            mprice = price_pat.search(txt)
            mqty = qty_pat.search(txt)
            if mprice and mqty:
                p = float(mprice.group(1))
                q = int(mqty.group(1))
                positions[symbol].append({'side':side,'entry_price':p,'qty':q,'open':True})
        # Exit: Target or Stoploss
        mexit = t1_pat.search(txt)
        if mexit and (mexit.group(1).startswith('T') or mexit.group(1).startswith('ST') or 'STOP LOSS' in mexit.group(1)):
            mprice = price_pat.search(txt)
            mqty = qty_pat.search(txt)
            if mprice and mqty:
                px = float(mprice.group(1))
                q = int(mqty.group(1))
                # Find latest open position of same side
                found = False
                for pos in positions[symbol]:
                    if pos['open'] and pos['qty'] == q and pos['side'] == side:
                        entry_px = pos['entry_price']
                        if side == 'BUY':
                            pl = (px - entry_px) * q
                        else:
                            pl = (entry_px - px) * q
                        realized_pl += pl
                        total_brokerage += BROKERAGE_FLAT_PER_SIDE + BROKERAGE_FLAT_PER_SIDE
                        pos['open'] = False
                        found = True
                        break
                if not found:
                    # Try find any open position to match qty
                    for pos in positions[symbol]:
                        if pos['open'] and pos['qty'] == q:
                            entry_px = pos['entry_price']
                            if pos['side'] == 'BUY':
                                pl = (px - entry_px) * q
                            else:
                                pl = (entry_px - px) * q
                            realized_pl += pl
                            total_brokerage += BROKERAGE_FLAT_PER_SIDE + BROKERAGE_FLAT_PER_SIDE
                            pos['open'] = False
                            break
    # All open positions at EOD
    for symbol, plist in positions.items():
        for pos in plist:
            if pos['open']:
                q = pos['qty']
                entry_px = pos['entry_price']
                side = pos['side']
                eod_px = last_prices.get(symbol)
                if eod_px:
                    if side == 'BUY':
                        pl = (eod_px - entry_px) * q
                    else:
                        pl = (entry_px - eod_px) * q
                    realized_pl += pl
                    total_brokerage += BROKERAGE_FLAT_PER_SIDE + BROKERAGE_FLAT_PER_SIDE
    net_profit = realized_pl - total_brokerage
    print(f"PnL from Telegram Alerts:")
    print(f"Total Profit: {realized_pl:.2f}")
    print(f"Total Brokerage: {total_brokerage:.2f}")
    print(f"Net Profit: {net_profit:.2f}")
    logger.info(f"PnL from Telegram Alerts | Profit: {realized_pl:.2f} | Brokerage: {total_brokerage:.2f} | Net: {net_profit:.2f}")


def _fmt_levels_row(prefix: str, lv: 'Levels') -> List[str]:
    return [
        f"{prefix} Buy Above: {lv.buy_above:.2f}",
        f"{prefix} T1..T5: {lv.t[0]:.2f}, {lv.t[1]:.2f}, {lv.t[2]:.2f}, {lv.t[3]:.2f}, {lv.t[4]:.2f}",
        f"{prefix} Buy SL: {lv.buy_sl:.2f}",
        f"{prefix} Sell Below: {lv.sell_below:.2f}",
        f"{prefix} ST1..ST5: {lv.st[0]:.2f}, {lv.st[1]:.2f}, {lv.st[2]:.2f}, {lv.st[3]:.2f}, {lv.st[4]:.2f}",
        f"{prefix} Sell SL: {lv.sell_sl:.2f}",
    ]


def build_premarket_adjustment_comparison_alert(symbol: str, old_lv: 'Levels', new_lv: 'Levels', current_price: float, status_line: str) -> str:
    ts = now_ist().strftime("%Y-%m-%d %H:%M:%S IST%z")
    lines: List[str] = []
    lines.append(f"🚨 {symbol} Alert at {ts}")
    lines.append("")
    lines.append(f"Previous Close: {new_lv.previous_close:.2f}")
    lines.append(f"Current Price: {current_price:.2f}")
    change_pct = ((current_price - new_lv.previous_close) / new_lv.previous_close * 100.0) if new_lv.previous_close else 0.0
    lines.append(f"Change: {_fmt_pct(change_pct)}")
    lines.append(f"Deviation (X): {new_lv.x:.2f}")
    lines.append(f"Status: {status_line}")
    lines.append("")
    lines.append("📊 Technical Analysis:")
    lines.extend(_fmt_levels_row("Initial", old_lv))
    lines.append("")
    lines.extend(_fmt_levels_row("Adjusted", new_lv))
    return "\n".join(lines)


# Realized P&L events per symbol for dashboard rendering
REALIZED_EVENTS: Dict[str, List[dict]] = {}
EVENTS_LOCK = threading.Lock()

def record_realized_event(symbol: str, side: str, event: str, price: float, qty: int, gross: float, net: float) -> None:
    with EVENTS_LOCK:
        if symbol not in REALIZED_EVENTS:
            REALIZED_EVENTS[symbol] = []
        REALIZED_EVENTS[symbol].append({
            'time': now_ist().strftime('%H:%M:%S'),
            'event': event,
            'side': side,
            'price': price,
            'qty': qty,
            'gross': gross,
            'net': net,
        })


if __name__ == "__main__":
    main()

