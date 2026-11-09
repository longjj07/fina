#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
A股 / 港股 / 美股 桌面看盘 + A股选股器 (零依赖: Python 标准库 + Tkinter)

数据源:
  - 自选股 / 指数: 新浪 hq.sinajs.cn 批量(主) + 腾讯 qt.gtimg.cn 回退
  - 美股数据:      Nasdaq summary/historical + Yahoo chart/news + SEC 财务
  - 加密货币:      Binance 24h ticker/日K/逐笔 (主) + OKX 回退
  - 选股器:        新浪 A股全市场列表 + 东财批量量比/换手, 腾讯单只回退
  - 历史日K:       腾讯 fqkline -> 新浪 -> Yahoo(港美股兜底)
  - 分笔成交:      腾讯(A股) / 东财(港美股) / Binance(加密) / Yahoo 1分钟分时
  - 综合评估:      基本面(腾讯估值字段) + 24h消息面 + K线技术面 + 买入区间
  - 因子选股:      factor_engine.py (个股/ETF/加密货币, RankIC/ICIR + 次日标注)
  - 问财选股:      同花顺 iwencai 自然语言筛选 (可选依赖 pywencai + Node.js + 登录cookie)
均为免费、免密钥、大陆可直连。行情为延时行情(美股/港股约15分钟, A股盘中约3秒), 仅供监控参考,
不构成任何投资建议。

运行:  python stock_monitor.py
"""

import csv
import importlib.util
import json
import logging
import math
import os
import queue
import shutil
import socket
import threading
import time
import urllib.request
import urllib.parse
import webbrowser
from concurrent.futures import ThreadPoolExecutor

import tkinter as tk
from tkinter import ttk, messagebox, filedialog

try:
    import factor_engine
except Exception:
    factor_engine = None

import tkinter as tk
from tkinter import ttk, messagebox

# ---------------------------------------------------------------------------
# 常量与配置
# ---------------------------------------------------------------------------

CONFIG_FILE = os.path.join(os.path.dirname(os.path.abspath(__file__)), "stock_monitor_config.json")

# 默认自选股: 美股 + A股 + 港股 混排示例
DEFAULT_WATCHLIST = [
    "AAPL", "MSFT", "NVDA", "GOOGL", "AMZN", "META", "TSLA", "AVGO", "AMD", "NFLX",
    "JPM", "V", "MA", "COST", "HD", "UNH", "XOM", "JNJ", "WMT", "PG",
    "600519", "300750", "000858", "00700", "09988", "03690",
    "BTC", "ETH",
]

# 顶部指数: (显示名, 腾讯代码)
INDEXES = [
    ("上证指数", "sh000001"),
    ("深证成指", "sz399001"),
    ("创业板指", "sz399006"),
    ("恒生指数", "hkHSI"),
    ("道琼斯",   "usDJI"),
    ("纳斯达克", "usIXIC"),
    ("标普500",  "usINX"),
]

MARKET_LABEL = {"us": "美股", "sh": "沪A", "sz": "深A", "bj": "北A", "hk": "港股", "cr": "加密货币"}

BINANCE_TICKER_URL = "https://api.binance.com/api/v3/ticker/24hr?symbols={symbols}"
BINANCE_KLINES_URL = ("https://api.binance.com/api/v3/klines?"
                      "symbol={sym}&interval=1d&limit={n}")
BINANCE_TRADES_URL = "https://api.binance.com/api/v3/trades?symbol={sym}&limit={n}"
OKX_TICKERS_URL = "https://www.okx.com/api/v5/market/tickers?instType=SPOT"
OKX_CANDLES_URL = "https://www.okx.com/api/v5/market/candles?instId={inst}&bar=1D&limit={n}"
OKX_TRADES_URL = "https://www.okx.com/api/v5/market/trades?instId={inst}&limit={n}"
NASDAQ_SUMMARY_URL = "https://api.nasdaq.com/api/quote/{sym}/summary?assetclass=stocks"
NASDAQ_HIST_URL = ("https://api.nasdaq.com/api/quote/{sym}/historical?assetclass=stocks"
                   "&fromdate={fromdate}&limit={n}")
# Yahoo 接口地址保留为可配置: FINA_YAHOO_BASE 可换成镜像/代理地址
YAHOO_BASE = os.environ.get("FINA_YAHOO_BASE",
                            "https://query1.finance.yahoo.com").rstrip("/")
YAHOO_SEARCH_URL = (YAHOO_BASE + "/v1/finance/search?"
                    "q={sym}&quotesCount=1&newsCount={n}")
SEC_TICKERS_URL = "https://www.sec.gov/files/company_tickers.json"
SEC_CONCEPT_URL = "https://data.sec.gov/api/xbrl/companyconcept/CIK{cik}/{tax}/{tag}.json"
SEC_UA = {"User-Agent": "fina-research/1.0 (research@example.com)"}

# 常见币种: 裸代码直接识别为加密货币; 其他币种可用 cr:代码 显式指定
CRYPTO_SYMBOLS = {
    "BTC", "ETH", "BNB", "SOL", "XRP", "ADA", "DOGE", "AVAX", "LINK", "DOT",
    "TRX", "TON", "SHIB", "LTC", "BCH", "UNI", "APT", "ARB", "OP", "SUI",
    "PEPE", "WIF", "NEAR", "ATOM", "FIL", "INJ", "SEI", "TIA", "ETC", "XLM",
    "HBAR", "ICP", "RENDER", "FET", "TAO", "ONDO", "JUP", "PYTH", "BONK",
    "FLOKI", "AAVE", "MKR", "CRV", "ALGO", "VET", "STX", "IMX", "GRT", "SAND",
    "MANA", "AXS", "GALA", "THETA", "RUNE", "KAS", "ENA", "WLD", "JTO", "STRK",
    "ZK", "PENDLE", "LDO", "EIGEN", "ZEC", "XMR", "DASH", "COMP", "SNX", "1INCH",
}
CRYPTO_STABLE = {
    "USDC", "FDUSD", "TUSD", "DAI", "USDP", "BUSD", "EUR", "AEUR", "USDD",
    "PYUSD", "USD1", "XAUT", "PAXG",
}

UA = {"User-Agent": "Mozilla/5.0 (Windows NT 10.0; Win64; x64)"}
SINA_HDR = {"User-Agent": UA["User-Agent"], "Referer": "https://finance.sina.com.cn/"}
SINA_LIST_URL = ("https://vip.stock.finance.sina.com.cn/quotes_service/api/json_v2.php/"
                 "Market_Center.getHQNodeData?page={page}&num={num}&sort=changepercent&asc=0&node=hs_a&symbol=")
EM_UT = "bd1d9ddb04089700cf9c27f6f7426281"
EM_HDR = {"User-Agent": UA["User-Agent"], "Referer": "https://quote.eastmoney.com/"}
EM_ULIST_URL = ("https://push2.eastmoney.com/api/qt/ulist.np/get?fltt=2&invt=2"
                "&secids={secids}&ut=" + EM_UT +
                "&fields=f2,f3,f4,f5,f6,f8,f10,f12,f13,f14,f15,f16,f17,f18,f124")
EM_DETAILS_URL = ("https://push2.eastmoney.com/api/qt/stock/details/get?secid={secid}"
                  "&ut=" + EM_UT +
                  "&fields1=f1,f2,f3,f4&fields2=f51,f52,f53,f54,f55&pos=-{n}")
EM_INDEX_SECIDS = {
    "sh000001": "1.000001",
    "sz399001": "0.399001",
    "sz399006": "0.399006",
    "hkHSI": "100.HSI",
    "usDJI": "100.DJIA",
    "usIXIC": "100.NDX",
    "usINX": "100.SPX",
}
EM_US_SUFFIX = {105: "OQ", 106: "N", 107: "A"}
SINA_HQ_URL = "https://hq.sinajs.cn/list={codes}"
YAHOO_CHART_URL = (YAHOO_BASE + "/v8/finance/chart/"
                   "{sym}?interval=1m&range=1d")
YAHOO_DAILY_URL = (YAHOO_BASE + "/v8/finance/chart/"
                   "{sym}?interval=1d&range=6mo")
_EM_QUOTE_OFF_UNTIL = 0.0
_EM_TICK_OFF_UNTIL = 0.0
_EM_OFF_TTL = 60.0


# ---------------------------------------------------------------------------
# 行情源: 新浪批量(主) -> 腾讯(兜底); 东财用于量比/换手与港美股分笔
# ---------------------------------------------------------------------------

def sina_code(raw):
    """A股/港股/指数用 sh600519 / hk00700 形式; 美股仍走腾讯(需要交易所后缀)。"""
    c = classify_symbol(raw)
    if not c or not raw:
        return None
    tcode, disp, mkt = c
    if mkt == "us":
        return None
    return tcode


def _parse_sina_block(code, body):
    p = body.split(",")
    if len(p) < 6:
        return None
    if code.startswith("gb_"):
        price = to_float(p[1])
        if price is None:
            return None
        pct = to_float(p[2])
        change = to_float(p[4])
        prev = to_float(p[26]) if len(p) > 26 else None
        if prev is None and pct not in (None, -100.0):
            prev = price / (1 + pct / 100.0)
        return {
            "name": p[0].strip(), "qt_code": p[0].strip(),
            "price": price, "change": change, "pct": pct,
            "open": to_float(p[5]), "high": to_float(p[6]), "low": to_float(p[7]),
            "prev_close": prev, "volume": to_float(p[10], 0),
            "time": (p[3] or "").strip()[11:19] or time.strftime("%H:%M:%S"),
            "source": "sina",
        }
    if code.startswith("hk"):
        price = to_float(p[6])
        prev = to_float(p[3])
        if price is None:
            return None
        return {
            "name": p[1].strip() or p[0].strip(), "qt_code": code[2:],
            "price": price, "change": to_float(p[7]), "pct": to_float(p[8]),
            "open": to_float(p[2]),
            "high": to_float(p[4]), "low": to_float(p[5]),
            "prev_close": prev, "volume": to_float(p[12], 0),
            "amount": to_float(p[11], 0),
            "time": (p[18] if len(p) > 18 else "").strip() or time.strftime("%H:%M:%S"),
            "source": "sina",
        }
    # A股 / 指数: 0名称 1开 2昨收 3现价 4高 5低 8成交量(股) 9成交额 30日期 31时间
    price = to_float(p[3])
    prev = to_float(p[2])
    if price is None:
        return None
    vol = to_float(p[8], 0)
    return {
        "name": p[0].strip(), "qt_code": code[2:],
        "price": price,
        "change": round(price - prev, 3) if prev else None,
        "pct": round((price - prev) / prev * 100, 2) if prev else None,
        "open": to_float(p[1]),
        "high": to_float(p[4]), "low": to_float(p[5]),
        "prev_close": prev,
        "volume": (vol or 0) / 100.0,
        "amount": to_float(p[9], 0),
        "time": (p[31] if len(p) > 31 else "").strip() or time.strftime("%H:%M:%S"),
        "source": "sina",
    }


def _fetch_sina_quotes(codes):
    out = {}
    for i in range(0, len(codes), 40):
        chunk = codes[i:i + 40]
        try:
            raw = _http(SINA_HQ_URL.format(codes=",".join(chunk)), SINA_HDR, timeout=6)
            text = raw.decode("gbk", "replace")
        except Exception:
            continue
        for line in text.split(";"):
            line = line.strip()
            if not line.startswith("var hq_str_"):
                continue
            head, _, rest = line.partition("=")
            code = head[len("var hq_str_"):].strip()
            if '"' not in rest:
                continue
            body = rest.split('"')[1]
            if not body:
                continue
            q = _parse_sina_block(code, body)
            if q:
                out[code] = q
    return out


def fetch_quotes_auto(items):
    """items = [(key, sina_code, tcode)]; 新浪整批 -> 腾讯补齐缺失。"""
    sina_codes = {}
    for key, scode, _tcode in items:
        if scode:
            sina_codes[scode] = key
    sina_rows = _fetch_sina_quotes(list(sina_codes)) if sina_codes else {}
    out = {}
    for scode, q in sina_rows.items():
        key = sina_codes.get(scode)
        if key:
            out[key] = q
    missing = [(k, t) for k, _s, t in items if k not in out]
    fallback = {"tencent": 0, "yahoo": 0, "eastmoney": 0}

    def fill(it):
        key, tcode = it
        q = fetch_yahoo_quote(tcode[2:]) if tcode.startswith("us") else None
        if not q:
            q = fetch_tencent_quote(tcode)
        if not q and tcode.startswith("us"):
            q = fetch_em_us_quote(tcode[2:])
        return key, q, (q or {}).get("source", "")

    if missing:
        with ThreadPoolExecutor(max_workers=min(8, len(missing))) as ex:
            for key, q, src in ex.map(fill, missing):
                if q:
                    out[key] = q
                    if src in fallback:
                        fallback[src] += 1
    return out, {"sina": len(out) - sum(fallback.values()), **fallback}


# 运行错误日志(排查界面/线程异常; 零依赖)
LOG_FILE = os.path.join(os.path.dirname(os.path.abspath(__file__)), "stock_monitor.log")
_LOG = logging.getLogger("fina")
_LOG.setLevel(logging.INFO)
if not _LOG.handlers:
    try:
        _lh = logging.FileHandler(LOG_FILE, encoding="utf-8")
        _lh.setFormatter(logging.Formatter("%(asctime)s %(levelname)s %(message)s"))
        _LOG.addHandler(_lh)
    except Exception:
        pass


def _log_thread_error(args):
    _LOG.error("线程未捕获异常", exc_info=(args.exc_type, args.exc_value,
                                           args.exc_traceback))


threading.excepthook = _log_thread_error

# 币安风格深色主题
BG_ROOT = "#0B0E11"
BG_PANEL = "#181A20"
BG_CARD = "#1E2329"
BG_HOVER = "#2B3139"
BORDER = "#2B3139"
FG_TEXT = "#EAECEF"
FG_MUTED = "#848E9C"
ACCENT = "#F0B90B"
ACCENT_HOVER = "#FCD535"

# 涨跌配色(默认红涨绿跌, 界面可切换; 币安红绿)
COLOR_UP_DEFAULT = "#F6465D"
COLOR_DOWN_DEFAULT = "#0ECB81"
COLOR_FLAT = "#848E9C"


# ---------------------------------------------------------------------------
# 基础工具
# ---------------------------------------------------------------------------

_PROXY_CHECK = {"ts": 0.0, "alive": None}
_DIRECT_OPENER = None
_HOST_OK_CACHE = {}


def _host_reachable(url, ttl=300.0):
    """快速判断海外源主机是否可达(1 秒 TCP 探测), 不可达时跳过以避免长超时。"""
    host = urllib.parse.urlsplit(url).hostname
    if not host:
        return False
    now = time.time()
    hit = _HOST_OK_CACHE.get(host)
    if hit and now - hit[0] < ttl:
        return hit[1]
    ok = False
    try:
        with socket.create_connection((host, 443), timeout=1.0):
            ok = True
    except Exception:
        ok = False
    _HOST_OK_CACHE[host] = (now, ok)
    return ok


# 海外源熔断: TCP 能连通但 HTTP 403/超时的源, 失败后暂停 10 分钟
_INTL_STATE = {}
_INTL_TTL = 600.0
_INTL_LOCK = threading.Lock()


def _intl_ok(name):
    with _INTL_LOCK:
        off = _INTL_STATE.get(name, 0.0)
        return time.time() >= off


def _intl_mark(name, ok):
    with _INTL_LOCK:
        _INTL_STATE[name] = 0.0 if ok else time.time() + _INTL_TTL


# 海外源可用性探测: 访问一次小样本, 失败则本机视为不可用, 10 分钟内直接跳过
_OVERSEAS_STATE = {}
_OVERSEAS_PROBES = {
    "yahoo": YAHOO_BASE + "/v8/finance/chart/SPY?interval=1d&range=1d",
    "nasdaq": NASDAQ_SUMMARY_URL.format(sym="AAPL"),
    "sec": "https://data.sec.gov/api/xbrl/companyconcept/CIK0000320193/us-gaap/Revenues.json",
    "binance": "https://api.binance.com/api/v3/ping",
    "okx": "https://www.okx.com/api/v5/public/time",
}


def _overseas_ok(name):
    now = time.time()
    hit = _OVERSEAS_STATE.get(name)
    if hit and now - hit[0] < 600:
        return hit[1]
    url = _OVERSEAS_PROBES.get(name)
    ok = False
    if url:
        try:
            _http(url, UA, timeout=3)
            ok = True
        except Exception:
            ok = False
    _OVERSEAS_STATE[name] = (now, ok)
    return ok


def _proxy_usable():
    """系统代理存在但进程未运行时返回 False, 改用直连。
    常见场景: Clash/V2Ray 关闭后 Windows 仍保留 127.0.0.1 代理设置,
    此时 urllib 会全部 ConnectionRefused, 而直连本身是通的。"""
    proxies = urllib.request.getproxies()
    p = proxies.get("https") or proxies.get("http")
    if not p:
        return True
    now = time.time()
    if _PROXY_CHECK["alive"] is not None and now - _PROXY_CHECK["ts"] < 30:
        return _PROXY_CHECK["alive"]
    alive = False
    try:
        hostport = p.split("://", 1)[-1].rstrip("/")
        host, _, port = hostport.partition(":")
        with socket.create_connection((host, int(port or 80)), timeout=0.8):
            alive = True
    except Exception:
        alive = False
    _PROXY_CHECK.update(ts=now, alive=alive)
    return alive


_DOMESTIC_HOSTS = ("eastmoney.com", "sinajs.cn", "sina.com.cn",
                   "gtimg.cn", "qq.com", "iwencai.com")


def _is_domestic(url):
    host = (urllib.parse.urlsplit(url).hostname or "").lower()
    return any(host == h or host.endswith("." + h) for h in _DOMESTIC_HOSTS)


def _http(url, headers, timeout=8):
    global _DIRECT_OPENER
    req = urllib.request.Request(url, headers=headers)
    if _is_domestic(url) or not _proxy_usable():
        if _DIRECT_OPENER is None:
            _DIRECT_OPENER = urllib.request.build_opener(urllib.request.ProxyHandler({}))
        with _DIRECT_OPENER.open(req, timeout=timeout) as r:
            return r.read()
    with urllib.request.urlopen(req, timeout=timeout) as r:
        return r.read()


def to_float(x, nd=2):
    """兼容数值或 "-" / 空串。"""
    if x is None:
        return None
    if isinstance(x, (int, float)):
        return round(float(x), nd)
    s = str(x).strip()
    if s in ("", "-", "--", "None", "null", "nan"):
        return None
    try:
        return round(float(s), nd)
    except (TypeError, ValueError):
        return None


def _raw_float(x, default=None):
    """不四舍五入的数值转换, 用于加密货币价格/数量。"""
    try:
        v = float(x)
        return v if math.isfinite(v) else default
    except (TypeError, ValueError):
        return default


def fmt_price(v):
    return "--" if v is None else f"{v:,.2f}"


def fmt_crypto_price(v):
    if v is None:
        return "--"
    try:
        v = float(v)
    except (TypeError, ValueError):
        return "--"
    a = abs(v)
    if a >= 1000:
        return f"{v:,.2f}"
    if a >= 1:
        return f"{v:,.3f}"
    if a >= 0.01:
        return f"{v:.4f}"
    if a >= 0.0001:
        return f"{v:.6f}"
    return f"{v:.8f}"


def fmt_crypto_qty(v):
    if v is None:
        return "--"
    try:
        v = float(v)
    except (TypeError, ValueError):
        return "--"
    a = abs(v)
    if a >= 1e6:
        return f"{v / 1e6:.2f}M"
    if a >= 1e3:
        return f"{v / 1e3:.2f}K"
    if a >= 1:
        return f"{v:,.3f}"
    return f"{v:.6f}"


def fmt_crypto_signed(v):
    if v is None:
        return "--"
    try:
        v = float(v)
    except (TypeError, ValueError):
        return "--"
    sign = "+" if v > 0 else ("-" if v < 0 else "")
    return sign + fmt_crypto_price(abs(v))


def fmt_signed(v):
    return "--" if v is None else f"{v:+,.2f}"


def fmt_pct(v):
    return "--" if v is None else f"{v:+.2f}%"


def fmt_pct_plain(v):
    return "--" if v is None else f"{v:.2f}%"


def fmt_vol(v):
    if v is None:
        return "--"
    v = float(v)
    if v >= 1e8:
        return f"{v / 1e8:.2f}亿"
    if v >= 1e4:
        return f"{v / 1e4:.2f}万"
    return f"{int(v):,}"


def fmt_amount(v):
    """成交额/市值: 亿元/万元。"""
    if v is None:
        return "--"
    v = float(v)
    if v >= 1e8:
        return f"{v / 1e8:.2f}亿"
    if v >= 1e4:
        return f"{v / 1e4:.2f}万"
    return f"{v:,.0f}"


# ---------------------------------------------------------------------------
# 腾讯行情解析(通用: 美股短格式 / A股港股指数长格式)
# ---------------------------------------------------------------------------

def parse_tencent(text):
    """解析 v_XXXX="...~..."。现价/昨收统一在 [3]/[4], 涨跌额与涨跌幅由二者计算;
    时间/最高/最低按字段数量区分(美股 30 字段为短格式, A股/港股/指数 >40 为长格式)。"""
    seg = text.split('"')[1]
    p = seg.split("~")
    if len(p) < 30:
        raise ValueError("腾讯返回字段不足")
    price = to_float(p[3])
    prev = to_float(p[4])
    change = round(price - prev, 2) if (price is not None and prev) else None
    pct = round((price - prev) / prev * 100, 2) if (price is not None and prev) else None
    long_fmt = len(p) > 40
    time_idx = 30 if long_fmt else 24
    high_idx = 33 if long_fmt else 27
    low_idx = 34 if long_fmt else 28
    ts = p[time_idx].strip()
    if ts.isdigit() and len(ts) == 14:   # A股紧凑时间 20260825152323 -> 可读格式
        ts = f"{ts[:4]}-{ts[4:6]}-{ts[6:8]} {ts[8:10]}:{ts[10:12]}:{ts[12:14]}"
    return {
        "name": p[1].strip(),
        "qt_code": p[2].strip(),       # 美股为带后缀完整代码(如 AAPL.OQ), 其余为数字代码
        "price": price,
        "change": change,
        "pct": pct,
        "open": to_float(p[5]),
        "high": to_float(p[high_idx]),
        "low": to_float(p[low_idx]),
        "prev_close": prev,
        "volume": to_float(p[6], 0),
        "time": ts,
    }


# ---------------------------------------------------------------------------
# 代码分类: 把用户输入映射为 (腾讯代码, 展示代码, 市场)
# ---------------------------------------------------------------------------

def classify_symbol(raw):
    s = (raw or "").strip().upper().replace(" ", "").replace("_", "")
    if not s:
        return None
    p2 = s[:2]
    # 显式前缀: sh600519 / sz000001 / bj430047 / hk00700 / usAAPL
    if p2 in ("SH", "SZ", "BJ") and len(s) == 8 and s[2:].isdigit():
        return p2.lower() + s[2:], s[2:], p2.lower()
    if p2 == "HK" and len(s) == 7 and s[2:].isdigit():
        return "hk" + s[2:], s[2:], "hk"
    if p2 == "US" and s[2:]:
        return "us" + s[2:], s[2:], "us"
    # 加密货币: CR:BTC / CR:BTCUSDT / 常见裸代码(BTC/ETH/SOL...)
    if s.startswith("CR:"):
        base = s[3:].replace("/", "").strip()
        if base.endswith("USDT"):
            base = base[:-4]
        if base:
            return "cr" + base + "USDT", base, "cr"
    if s in CRYPTO_SYMBOLS:
        return "cr" + s + "USDT", s, "cr"
    # 纯数字
    if s.isdigit():
        if len(s) == 5:
            return "hk" + s, s, "hk"          # 港股 5 位
        if len(s) == 6:
            c = s[0]
            if c in "569":
                return "sh" + s, s, "sh"      # 沪市股票/ETF/B股
            if c in "023":
                return "sz" + s, s, "sz"      # 深市
            if c in "48":
                return "bj" + s, s, "bj"      # 北交所
            return "sz" + s, s, "sz"
    # 字母(可含 . 或 -) -> 美股
    return "us" + s, s, "us"


# ---------------------------------------------------------------------------
# 行情源: 东方财富批量快照(主) + 腾讯(回退) + 分笔成交
# ---------------------------------------------------------------------------

def em_quote_candidates(raw):
    """代码 -> 东财 secid 候选。美股未知交易所, 同时尝试 NASDAQ/NYSE/AMEX。"""
    s = (raw or "").strip()
    if not s:
        return []
    if s in EM_INDEX_SECIDS:
        return [EM_INDEX_SECIDS[s]]
    c = classify_symbol(s)
    if not c:
        return []
    _tcode, disp, mkt = c
    if mkt == "sh":
        return ["1." + disp]
    if mkt in ("sz", "bj"):
        return ["0." + disp]
    if mkt == "hk":
        return ["116." + disp]
    if mkt == "us":
        out = [f"105.{disp}", f"106.{disp}", f"107.{disp}"]
        if "." in disp:
            alt = disp.replace(".", "-")
            out += [f"105.{alt}", f"106.{alt}", f"107.{alt}"]
        return out
    return []


def _fetch_em_quote_rows(secids):
    global _EM_QUOTE_OFF_UNTIL
    if time.time() < _EM_QUOTE_OFF_UNTIL:
        return {}
    rows = {}
    uniq = []
    seen = set()
    for s in secids:
        if s and s not in seen:
            seen.add(s)
            uniq.append(s)
    for i in range(0, len(uniq), 80):
        batch = uniq[i:i + 80]
        try:
            raw = _http(EM_ULIST_URL.format(secids=",".join(batch)), EM_HDR, timeout=6)
            data = json.loads(raw.decode("utf-8", "replace"))
        except Exception:
            _EM_QUOTE_OFF_UNTIL = time.time() + _EM_OFF_TTL
            break
        for row in (data.get("data") or {}).get("diff") or []:
            code = str(row.get("f12") or "")
            mkt = row.get("f13")
            if code:
                rows[f"{mkt}.{code}"] = row
    if rows:
        _EM_QUOTE_OFF_UNTIL = 0.0
    return rows


def _em_quote_from_row(row):
    price = to_float(row.get("f2"))
    if price is None:
        return None
    code = str(row.get("f12") or "")
    mkt = row.get("f13")
    suffix = EM_US_SUFFIX.get(mkt)
    qt_code = f"{code}.{suffix}" if suffix else code
    try:
        ts = time.strftime("%H:%M:%S", time.localtime(float(row.get("f124"))))
    except (TypeError, ValueError, OSError, OverflowError):
        ts = time.strftime("%H:%M:%S")
    return {
        "name": str(row.get("f14") or ""),
        "qt_code": qt_code,
        "price": price,
        "change": to_float(row.get("f4")),
        "pct": to_float(row.get("f3")),
        "open": to_float(row.get("f17")),
        "high": to_float(row.get("f15")),
        "low": to_float(row.get("f16")),
        "prev_close": to_float(row.get("f18")),
        "volume": to_float(row.get("f5"), 0),
        "amount": to_float(row.get("f6"), 0),
        "turnover": to_float(row.get("f8")),
        "volume_ratio": to_float(row.get("f10")),
        "time": ts,
        "source": "eastmoney",
    }


def fetch_em_quotes(items):
    """items = [(key, [secid...]), ...] -> {key: quote}"""
    secids = []
    for _key, cands in items:
        secids.extend(cands)
    rows = _fetch_em_quote_rows(secids)
    out = {}
    for key, cands in items:
        for secid in cands:
            row = rows.get(secid)
            if row:
                q = _em_quote_from_row(row)
                if q:
                    out[key] = q
                    break
    return out


def fetch_tencent_batch(tcodes):
    """腾讯批量报价: tcodes 形如 ['usAAPL','usMSFT']。"""
    out = {}
    uniq = list(dict.fromkeys(t for t in tcodes if t))
    for i in range(0, len(uniq), 50):
        chunk = uniq[i:i + 50]
        try:
            raw = _http("https://qt.gtimg.cn/q=" + ",".join(chunk), UA,
                        timeout=8).decode("gbk", "replace")
        except Exception:
            continue
        for line in raw.split(";"):
            line = line.strip()
            if not line.startswith("v_") or '"' not in line:
                continue
            try:
                q = parse_tencent(line)
            except Exception:
                continue
            code = line[2:line.find("=")].strip()
            out[code] = q
    return out


def fetch_tencent_quote(tcode):
    try:
        raw = _http("https://qt.gtimg.cn/q=" + tcode, UA).decode("gbk", "replace")
        q = parse_tencent(raw)
        q["source"] = "tencent"
        return q
    except Exception:
        return None


def _crypto_pair(raw):
    c = classify_symbol(raw)
    if not c or c[2] != "cr":
        return None
    return c[0][2:]          # crBTCUSDT -> BTCUSDT


def _utc_date(ms):
    return time.strftime("%Y-%m-%d", time.gmtime(float(ms) / 1000.0))


def _crypto_quote_from_binance(row, raw):
    price = _raw_float(row.get("lastPrice"))
    if price is None:
        return None
    pair = str(row.get("symbol") or "")
    return {
        "name": pair[:-4] if pair.endswith("USDT") else pair,
        "qt_code": pair,
        "price": price,
        "change": _raw_float(row.get("priceChange")),
        "pct": _raw_float(row.get("priceChangePercent")),
        "open": _raw_float(row.get("openPrice")),
        "high": _raw_float(row.get("highPrice")),
        "low": _raw_float(row.get("lowPrice")),
        "prev_close": _raw_float(row.get("openPrice")),
        "volume": _raw_float(row.get("volume"), 0),
        "amount": _raw_float(row.get("quoteVolume"), 0),
        "time": time.strftime("%H:%M:%S", time.localtime(float(row.get("closeTime") or 0) / 1000.0)),
        "source": "binance",
    }


def fetch_crypto_quotes(raw_symbols):
    """Binance 24h ticker 批量; 缺失项用 OKX 补齐。"""
    pairs = {}
    for raw in raw_symbols:
        pair = _crypto_pair(raw)
        if pair:
            pairs[pair] = raw
    out = {}
    if not pairs:
        return out, "binance"
    if _overseas_ok("binance"):
        try:
            sym_json = urllib.parse.quote(json.dumps(list(pairs), separators=(",", ":")))
            raw = _http(BINANCE_TICKER_URL.format(symbols=sym_json), UA, timeout=8)
            arr = json.loads(raw.decode("utf-8", "replace"))
            for row in arr if isinstance(arr, list) else []:
                pair = str(row.get("symbol") or "")
                source_raw = pairs.get(pair)
                if not source_raw:
                    continue
                q = _crypto_quote_from_binance(row, source_raw)
                if q:
                    out[source_raw] = q
        except Exception:
            pass
    missing = [p for p, raw in pairs.items() if raw not in out]
    if missing and _overseas_ok("okx"):
        try:
            raw = _http(OKX_TICKERS_URL, UA, timeout=8)
            data = json.loads(raw.decode("utf-8", "replace"))
            okx = {}
            for row in (data.get("data") or []):
                inst = str(row.get("instId") or "")
                if inst.endswith("-USDT"):
                    okx[inst.replace("-", "")] = row
            for pair in missing:
                row = okx.get(pair)
                if not row:
                    continue
                last = _raw_float(row.get("last"))
                open24 = _raw_float(row.get("open24h"))
                if last is None:
                    continue
                change = (last - open24) if open24 not in (None, 0) else None
                pct = (change / open24 * 100.0) if open24 else None
                base = pair[:-4] if pair.endswith("USDT") else pair
                out[pairs[pair]] = {
                    "name": base, "qt_code": pair,
                    "price": last, "change": change, "pct": pct,
                    "open": open24,
                    "high": _raw_float(row.get("high24h")),
                    "low": _raw_float(row.get("low24h")),
                    "prev_close": open24,
                    "volume": _raw_float(row.get("vol24h"), 0),
                    "amount": _raw_float(row.get("volCcy24h"), 0),
                    "time": time.strftime("%H:%M:%S", time.localtime(float(row.get("ts") or 0) / 1000.0)),
                    "source": "okx",
                }
        except Exception:
            pass
    return out, "binance"


def fetch_crypto_bars(pair, n=320):
    """Binance 日K(UTC); 失败回退 OKX。去掉当日未收盘 bar。"""
    today = time.strftime("%Y-%m-%d", time.gmtime())
    try:
        raw = _http(BINANCE_KLINES_URL.format(sym=pair, n=n), UA, timeout=8)
        arr = json.loads(raw.decode("utf-8", "replace"))
        bars = []
        for k in arr if isinstance(arr, list) else []:
            if not isinstance(k, (list, tuple)) or len(k) < 6:
                continue
            bars.append({
                "date": _utc_date(k[0]),
                "open": _raw_float(k[1]), "high": _raw_float(k[2]),
                "low": _raw_float(k[3]), "close": _raw_float(k[4]),
                "volume": _raw_float(k[5], 0),
            })
        bars = [b for b in bars if b["close"] is not None and b["date"] <= today]
        if bars and bars[-1]["date"] == today:
            bars = bars[:-1]          # 当日 UTC 日K未收盘
        if bars:
            return bars
    except Exception:
        pass
    try:
        inst = pair[:-4] + "-USDT" if pair.endswith("USDT") else pair
        raw = _http(OKX_CANDLES_URL.format(inst=inst, n=n), UA, timeout=8)
        data = json.loads(raw.decode("utf-8", "replace"))
        bars = []
        for k in (data.get("data") or []):
            if len(k) < 6:
                continue
            bars.append({
                "date": _utc_date(k[0]),
                "open": _raw_float(k[1]), "high": _raw_float(k[2]),
                "low": _raw_float(k[3]), "close": _raw_float(k[4]),
                "volume": _raw_float(k[5], 0),
            })
        bars.sort(key=lambda b: b["date"])
        bars = [b for b in bars if b["close"] is not None and b["date"] <= today]
        if bars and bars[-1]["date"] == today:
            bars = bars[:-1]
        return bars
    except Exception:
        return []


def fetch_crypto_trades(pair, n=50):
    try:
        raw = _http(BINANCE_TRADES_URL.format(sym=pair, n=max(20, min(100, n))),
                    UA, timeout=8)
        arr = json.loads(raw.decode("utf-8", "replace"))
        rows = []
        for i, t in enumerate(arr if isinstance(arr, list) else []):
            price = _raw_float(t.get("price"))
            if price is None:
                continue
            maker = bool(t.get("isBuyerMaker"))
            rows.append({
                "index": i,
                "time": time.strftime("%H:%M:%S",
                                      time.localtime(float(t.get("time") or 0) / 1000.0)),
                "price": price,
                "volume": _raw_float(t.get("qty"), 0),
                "amount": _raw_float(t.get("quoteQty"), 0),
                "direction": "卖" if maker else "买",
            })
        return rows
    except Exception:
        pass
    try:
        inst = pair[:-4] + "-USDT" if pair.endswith("USDT") else pair
        raw = _http(OKX_TRADES_URL.format(inst=inst, n=max(20, min(100, n))),
                    UA, timeout=8)
        data = json.loads(raw.decode("utf-8", "replace"))
        rows = []
        for i, t in enumerate(data.get("data") or []):
            price = _raw_float(t.get("px"))
            if price is None:
                continue
            rows.append({
                "index": i,
                "time": time.strftime("%H:%M:%S",
                                      time.localtime(float(t.get("ts") or 0) / 1000.0)),
                "price": price,
                "volume": _raw_float(t.get("sz"), 0),
                "amount": None,
                "direction": "买" if str(t.get("side")) == "buy" else "卖",
            })
        return rows
    except Exception:
        return []


def _us_ticker(raw):
    c = classify_symbol(raw)
    if not c or c[2] != "us":
        return None
    disp = c[1]
    for suf in (".OQ", ".N", ".A"):
        if disp.endswith(suf):
            disp = disp[:-3]
            break
    return disp


def _money(v):
    s = str(v or "").replace("$", "").replace(",", "").replace("%", "").strip()
    if s in ("", "N/A", "--", "-", "None"):
        return None
    try:
        return float(s)
    except (TypeError, ValueError):
        return None


def _split_52(v):
    parts = str(v or "").replace("$", "").replace(",", "").split("/")
    if len(parts) < 2:
        return None, None
    try:
        return float(parts[1]), float(parts[0])   # low, high
    except (TypeError, ValueError):
        return None, None


_US_QT_CACHE = {}


def _us_tencent_code(symbol):
    if not symbol.startswith("us"):
        return symbol
    disp = symbol[2:]
    if any(disp.endswith(x) for x in (".OQ", ".N", ".A")):
        return symbol
    hit = _US_QT_CACHE.get(disp)
    if hit:
        return "us" + hit
    q = fetch_tencent_quote("us" + disp)
    code = (q or {}).get("qt_code") or ""
    if "." in code:
        _US_QT_CACHE[disp] = code
        return "us" + code
    return symbol


_NASDAQ_SUMMARY_CACHE = {}
_NASDAQ_HIST_CACHE = {}
_YAHOO_NEWS_CACHE = {}


def fetch_nasdaq_summary(sym):
    sym = (sym or "").upper()
    if (not sym or not _host_reachable(NASDAQ_SUMMARY_URL)
            or not _intl_ok("nasdaq") or not _overseas_ok("nasdaq")):
        return {}
    hit = _NASDAQ_SUMMARY_CACHE.get(sym)
    if hit and time.time() - hit[0] < 300:
        return hit[1]
    try:
        hdr = {"User-Agent": UA["User-Agent"], "Referer": "https://www.nasdaq.com/",
               "Accept": "application/json, text/plain, */*"}
        raw = _http(NASDAQ_SUMMARY_URL.format(sym=sym), hdr, timeout=8)
        sd = (json.loads(raw.decode("utf-8", "replace")).get("data") or {}).get("summaryData") or {}
        low52, high52 = _split_52((sd.get("FiftTwoWeekHighLow") or {}).get("value"))
        out = {
            "sector": (sd.get("Sector") or {}).get("value"),
            "industry": (sd.get("Industry") or {}).get("value"),
            "mktcap": _money((sd.get("MarketCap") or {}).get("value")),
            "high52": high52, "low52": low52,
            "avg_volume": _money((sd.get("AverageVolume") or {}).get("value")),
            "one_year_target": _money((sd.get("OneYrTarget") or {}).get("value")),
            "prev_close": _money((sd.get("PreviousClose") or {}).get("value")),
            "dividend": _money((sd.get("AnnualizedDividend") or {}).get("value")),
            "yield": _money((sd.get("Yield") or {}).get("value")),
            "source": "nasdaq",
        }
        _NASDAQ_SUMMARY_CACHE[sym] = (time.time(), out)
        _intl_mark("nasdaq", True)
        return out
    except Exception:
        _intl_mark("nasdaq", False)
        return {}


def fetch_nasdaq_daily(sym, n=120):
    sym = (sym or "").upper()
    if (not sym or not _host_reachable(NASDAQ_HIST_URL)
            or not _intl_ok("nasdaq") or not _overseas_ok("nasdaq")):
        return []
    hit = _NASDAQ_HIST_CACHE.get(sym)
    if hit and time.time() - hit[0] < 300:
        return hit[1][-n:]
    try:
        fromdate = time.strftime("%Y-%m-%d",
                                 time.localtime(time.time() - max(60, n * 2) * 86400))
        hdr = {"User-Agent": UA["User-Agent"], "Referer": "https://www.nasdaq.com/",
               "Accept": "application/json, text/plain, */*"}
        raw = _http(NASDAQ_HIST_URL.format(sym=sym, fromdate=fromdate, n=n), hdr, timeout=8)
        rows = (((json.loads(raw.decode("utf-8", "replace")).get("data") or {})
                 .get("tradesTable") or {}).get("rows") or [])
        bars = []
        for r in rows:
            try:
                dt = time.strptime(str(r.get("date") or ""), "%m/%d/%Y")
                date = time.strftime("%Y-%m-%d", dt)
            except Exception:
                continue
            c = _money(r.get("close"))
            if c is None:
                continue
            bars.append({"date": date, "open": _money(r.get("open")),
                         "close": c, "high": _money(r.get("high")),
                         "low": _money(r.get("low")),
                         "volume": _money(r.get("volume")) or 0})
        bars.sort(key=lambda b: b["date"])
        _NASDAQ_HIST_CACHE[sym] = (time.time(), bars)
        _intl_mark("nasdaq", True)
        return bars[-n:]
    except Exception:
        _intl_mark("nasdaq", False)
        return []


def fetch_yahoo_news(sym, n=6):
    sym = (sym or "").upper()
    if (not sym or not _host_reachable(YAHOO_SEARCH_URL)
            or not _intl_ok("yahoo") or not _overseas_ok("yahoo")):
        return []
    hit = _YAHOO_NEWS_CACHE.get(sym)
    if hit and time.time() - hit[0] < 300:
        return hit[1][:n]
    try:
        raw = _http(YAHOO_SEARCH_URL.format(sym=sym, n=max(3, n)), UA, timeout=10)
        data = json.loads(raw.decode("utf-8", "replace"))
        out = []
        for it in data.get("news") or []:
            ts = it.get("providerPublishTime")
            t = time.strftime("%m-%d %H:%M", time.localtime(float(ts))) if ts else ""
            title = str(it.get("title") or "")
            out.append({"time": t, "title": title,
                        "url": it.get("link") or "",
                        "publisher": str(it.get("publisher") or ""),
                        "impact": classify_announcement(title)})
        _YAHOO_NEWS_CACHE[sym] = (time.time(), out)
        _intl_mark("yahoo", True)
        return out[:n]
    except Exception:
        _intl_mark("yahoo", False)
        return []


def fetch_yahoo_quote(sym):
    sym = (sym or "").upper().replace(".OQ", "").replace(".N", "").replace(".A", "")
    if (not _host_reachable(YAHOO_CHART_URL)
            or not _intl_ok("yahoo") or not _overseas_ok("yahoo")):
        return None
    try:
        raw = _http(YAHOO_CHART_URL.format(sym=sym), UA, timeout=8)
        res = ((json.loads(raw.decode("utf-8", "replace")).get("chart") or {})
               .get("result") or [])
        if not res:
            return None
        meta = res[0].get("meta") or {}
        price = _raw_float(meta.get("regularMarketPrice"))
        prev = _raw_float(meta.get("previousClose") or meta.get("chartPreviousClose"))
        if price is None:
            return None
        ts = meta.get("regularMarketTime")
        out = {
            "name": meta.get("longName") or meta.get("shortName") or sym,
            "qt_code": sym, "price": price,
            "change": (price - prev) if prev else None,
            "pct": ((price / prev - 1) * 100) if prev else None,
            "open": None,
            "high": _raw_float(meta.get("regularMarketDayHigh")),
            "low": _raw_float(meta.get("regularMarketDayLow")),
            "prev_close": prev,
            "volume": _raw_float(meta.get("regularMarketVolume"), 0),
            "time": time.strftime("%H:%M:%S", time.localtime(float(ts))) if ts else "",
            "source": "yahoo",
        }
        _intl_mark("yahoo", True)
        return out
    except Exception:
        _intl_mark("yahoo", False)
        return None


_EM_US_DETAIL_CACHE = {}
_EM_US_SECID_CACHE = {}
_EM_US_QUOTE_CACHE = {}
EM_US_DETAIL_URL = ("https://push2.eastmoney.com/api/qt/stock/get?secid={secid}"
                    "&ut=" + EM_UT +
                    "&fields=f43,f57,f58,f60,f84,f85,f116,f117,f127,f162,f167,"
                    "f168,f169,f170,f174,f175,f100")


def _em_us_secid(code):
    """美股代码 -> 东财 secid; 依次尝试纳斯达克/纽交所/美交所。"""
    raw = str(code or "").upper().replace(".", "_")
    sid = _EM_US_SECID_CACHE.get(raw)
    if sid:
        try:
            raw_b = _http(EM_US_DETAIL_URL.format(secid=sid), EM_HDR, timeout=5)
            data = json.loads(raw_b.decode("utf-8", "replace")).get("data") or {}
            if data.get("f57"):
                return sid, data
        except Exception:
            pass
    for mkt in (105, 106, 107):
        secid = f"{mkt}.{raw}"
        try:
            raw_b = _http(EM_US_DETAIL_URL.format(secid=secid), EM_HDR, timeout=5)
            data = json.loads(raw_b.decode("utf-8", "replace")).get("data") or {}
            if data.get("f57"):
                _EM_US_SECID_CACHE[raw] = secid
                return secid, data
        except Exception:
            continue
    return None, {}


def fetch_em_us_quote(code):
    """东方财富美股快照(国内直连), 用于腾讯/海外源不可达时的自选行情。"""
    key = str(code or "").upper()
    hit = _EM_US_QUOTE_CACHE.get(key)
    if hit and time.time() - hit[0] < 10:
        return dict(hit[1])
    _secid, d = _em_us_secid(key)
    if not d:
        return None

    def px(v):
        v = _raw_float(v)
        return v / 1000.0 if v is not None else None

    price = px(d.get("f43"))
    if price is None or price <= 0:
        return None
    pct = _raw_float(d.get("f170"))
    out = {
        "name": d.get("f58") or key,
        "qt_code": d.get("f57") or key,
        "price": price,
        "change": px(d.get("f169")),
        "pct": pct / 100.0 if pct is not None else None,
        "open": px(d.get("f46")),
        "high": px(d.get("f44")),
        "low": px(d.get("f45")),
        "prev_close": px(d.get("f60")),
        "volume": _raw_float(d.get("f47"), 0),
        "time": time.strftime("%H:%M:%S"),
        "source": "eastmoney",
    }
    _EM_US_QUOTE_CACHE[key] = (time.time(), dict(out))
    return out


def fetch_em_us_fundamentals(code):
    """东方财富美股基本面(国内直连), 作为 Nasdaq/SEC 不可达时的替代。"""
    code = (code or "").upper()
    hit = _EM_US_DETAIL_CACHE.get(code)
    if hit and time.time() - hit[0] < 600:
        return hit[1]
    secid, d = _em_us_secid(code)
    if not secid:
        _EM_US_DETAIL_CACHE[code] = (time.time(), {})
        return {}

    def px(v):
        v = _raw_float(v)
        return v / 1000.0 if v else None

    pb = _raw_float(d.get("f167"))
    out = {
        "pb": pb / 100.0 if pb and pb > 0 else None,
        "mktcap": (_raw_float(d.get("f116")) or 0) / 1e8 or None,
        "turnover": (_raw_float(d.get("f168")) or 0) / 100.0 or None,
        "high52": px(d.get("f174")),
        "low52": px(d.get("f175")),
        "prev_close": px(d.get("f60")),
        "industry": (d.get("f127") or d.get("f100")
                     if (d.get("f127") or d.get("f100")) not in (None, "-") else None),
        "name": d.get("f58"),
        "secid": secid,
        "source": "eastmoney",
    }
    out = {k: v for k, v in out.items() if v is not None}
    _EM_US_DETAIL_CACHE[code] = (time.time(), out)
    return out


_SEC_CIK = None
_SEC_CIK_FILE = os.path.join(os.path.dirname(os.path.abspath(__file__)), "sec_tickers.json")
_SEC_FUND_CACHE = {}


def _sec_cik_map():
    global _SEC_CIK
    if _SEC_CIK is not None:
        return _SEC_CIK
    data = None
    try:
        with open(_SEC_CIK_FILE, "r", encoding="utf-8") as f:
            data = json.load(f)
    except Exception:
        if (not _host_reachable(SEC_TICKERS_URL)
                or not _intl_ok("sec") or not _overseas_ok("sec")):
            data = {}
        else:
            try:
                raw = _http(SEC_TICKERS_URL, SEC_UA, timeout=20)
                data = json.loads(raw.decode("utf-8", "replace"))
                with open(_SEC_CIK_FILE, "w", encoding="utf-8") as f:
                    json.dump(data, f, ensure_ascii=False, separators=(",", ":"))
            except Exception:
                data = {}
    out = {}
    for v in (data or {}).values():
        try:
            out[str(v.get("ticker") or "").upper()] = str(v.get("cik_str") or "").zfill(10)
        except Exception:
            pass
    _SEC_CIK = out
    return out


def _sec_annual(vals, unit):
    arr = [x for x in (vals.get(unit) or [])
           if x.get("form") in ("10-K", "10-K/A") and x.get("fp") == "FY"
           and x.get("val") is not None]
    arr.sort(key=lambda x: (x.get("end") or "", x.get("filed") or ""))
    uniq = {}
    for x in arr:
        uniq[x.get("end")] = x
    seq = [uniq[k] for k in sorted(uniq)]
    if not seq:
        return None, None
    return seq[-1], (seq[-2] if len(seq) >= 2 else None)


def _sec_concept(cik, tax, tag):
    if not _intl_ok("sec") or not _overseas_ok("sec"):
        return {}
    try:
        raw = _http(SEC_CONCEPT_URL.format(cik=cik, tax=tax, tag=tag),
                    SEC_UA, timeout=6)
        return json.loads(raw.decode("utf-8", "replace")).get("units") or {}
    except Exception:
        return {}


def fetch_sec_fundamentals(sym):
    sym = (sym or "").upper()
    if (not _host_reachable(SEC_CONCEPT_URL)
            or not _intl_ok("sec") or not _overseas_ok("sec")):
        return {}
    hit = _SEC_FUND_CACHE.get(sym)
    if hit and time.time() - hit[0] < 3600:
        return hit[1]
    cik = _sec_cik_map().get(sym)
    if not cik:
        return {}
    tags = [
        ("revenue", "us-gaap", "RevenueFromContractWithCustomerExcludingAssessedTax", "USD"),
        ("revenue_fb", "us-gaap", "Revenues", "USD"),
        ("net_income", "us-gaap", "NetIncomeLoss", "USD"),
        ("equity", "us-gaap", "StockholdersEquity", "USD"),
        ("eps", "us-gaap", "EarningsPerShareDiluted", "USD/shares"),
        ("shares", "dei", "EntityCommonStockSharesOutstanding", "shares"),
    ]
    got = {}
    with ThreadPoolExecutor(max_workers=6) as ex:
        futs = {k: ex.submit(_sec_concept, cik, tax, tag) for k, tax, tag, _u in tags}
        for k, _tax, _tag, _unit in tags:
            try:
                got[k] = futs[k].result()
            except Exception:
                got[k] = {}
    rev_last, rev_prev = _sec_annual(got["revenue"], "USD")
    if not rev_last:
        rev_last, rev_prev = _sec_annual(got["revenue_fb"], "USD")
    ni_last, _ni_prev = _sec_annual(got["net_income"], "USD")
    eq_last, _eq_prev = _sec_annual(got["equity"], "USD")
    eps_last, _eps_prev = _sec_annual(got["eps"], "USD/shares")
    sh_last, _sh_prev = _sec_annual(got["shares"], "shares")
    out = {}
    if rev_last:
        out["revenue"] = rev_last.get("val")
        out["revenue_asof"] = rev_last.get("end")
        if rev_prev and rev_prev.get("val"):
            out["revenue_growth"] = rev_last["val"] / rev_prev["val"] - 1
    if ni_last:
        out["net_income"] = ni_last.get("val")
    if eq_last:
        out["equity"] = eq_last.get("val")
    if eps_last:
        out["eps"] = eps_last.get("val")
    if sh_last:
        out["shares"] = sh_last.get("val")
    if out.get("net_income") and out.get("revenue"):
        out["net_margin"] = out["net_income"] / out["revenue"]
    if out.get("net_income") and out.get("equity"):
        out["roe"] = out["net_income"] / out["equity"]
    _SEC_FUND_CACHE[sym] = (time.time(), out)
    _intl_mark("sec", bool(got and any(got.values())))
    return out


def _fetch_em_ticks(secid, n=50):
    global _EM_TICK_OFF_UNTIL
    if time.time() < _EM_TICK_OFF_UNTIL:
        return []
    # 东财 pos 是分页位置: -50 附近为最近成交; 过大反而会落到早盘
    n = max(20, min(50, int(n)))
    try:
        raw = _http(EM_DETAILS_URL.format(secid=secid, n=n), EM_HDR, timeout=6)
        data = json.loads(raw.decode("utf-8", "replace"))
    except Exception:
        _EM_TICK_OFF_UNTIL = time.time() + _EM_OFF_TTL
        raise
    rows = []
    for line in (data.get("data") or {}).get("details") or []:
        p = str(line).split(",")
        if len(p) < 4:
            continue
        price = to_float(p[1])
        if price is None:
            continue
        bs = p[4].strip() if len(p) > 4 else ""
        rows.append({
            "time": p[0],
            "price": price,
            "volume": to_float(p[2]),
            "amount": to_float(p[3]),
            "direction": "买" if bs == "1" else ("卖" if bs == "2" else "中性"),
        })
    return rows


def _fetch_tencent_ticks_page(tcode, page):
    try:
        url = ("https://stock.gtimg.cn/data/index.php?appn=detail&action=data"
               f"&c={tcode}&p={page}")
        hdr = {"User-Agent": UA["User-Agent"], "Referer": "https://gu.qq.com/"}
        text = _http(url, hdr, timeout=6).decode("utf-8", "replace")
        a, b = text.find('"'), text.rfind('"')
        if a < 0 or b <= a:
            return []
        rows = []
        for item in text[a + 1:b].split("|"):
            p = item.split("/")
            if len(p) < 7:
                continue
            price = to_float(p[2])
            if price is None:
                continue
            rows.append({
                "index": int(p[0]) if p[0].isdigit() else 0,
                "time": p[1],
                "price": price,
                "volume": to_float(p[4]),
                "amount": to_float(p[5]),
                "direction": {"B": "买", "S": "卖"}.get(p[6].strip(), "中性"),
            })
        return rows
    except Exception:
        return []


_TICK_LAST_PAGE = {}


def _fetch_tencent_ticks(tcode):
    """腾讯分笔按页返回; 自动定位最后一页, 缓存页号避免重复扫描。"""
    known = _TICK_LAST_PAGE.get(tcode)
    if known is None:
        first = _fetch_tencent_ticks_page(tcode, 0)
        if not first:
            return []
        lo, hi = 0, 1
        while hi <= 256:
            rows = _fetch_tencent_ticks_page(tcode, hi)
            if not rows:
                break
            lo, hi = hi, hi * 2
        while lo + 1 < hi:
            mid = (lo + hi) // 2
            if _fetch_tencent_ticks_page(tcode, mid):
                lo = mid
            else:
                hi = mid
        known = lo
    else:
        while known < 512 and _fetch_tencent_ticks_page(tcode, known + 1):
            known += 1
    _TICK_LAST_PAGE[tcode] = known
    rows = []
    for pg in (known - 1, known):
        if pg >= 0:
            rows.extend(_fetch_tencent_ticks_page(tcode, pg))
    dedup = {r["index"]: r for r in rows}
    ordered = [dedup[k] for k in sorted(dedup)]
    return ordered[-140:]


def fetch_ticks(code, n=50):
    c = classify_symbol(code)
    if c and c[2] == "cr":
        rows = fetch_crypto_trades(c[0][2:], n)
        if rows:
            return rows, "Binance"
    # A股逐笔优先用腾讯(稳定、字段清晰); 港股/美股用东财
    if c and c[2] in ("sh", "sz", "bj"):
        rows = _fetch_tencent_ticks(c[0])
        if rows:
            return rows, "腾讯"
    for secid in em_quote_candidates(code):
        try:
            rows = _fetch_em_ticks(secid, n)
            if rows:
                return rows, "东财"
        except Exception:
            continue
    if c:
        rows = _fetch_yahoo_minutes(code, max(20, n))
        if rows:
            return rows, "Yahoo分时"
    return [], ""


def _yahoo_symbol(code):
    c = classify_symbol(code)
    if not c:
        return None
    _tcode, disp, mkt = c
    if mkt == "us":
        # 腾讯后缀 .OQ/.N/.A 需先剥离; Yahoo 用 BRK-B 形式
        if "." in disp and disp.rsplit(".", 1)[-1] in ("OQ", "N", "A"):
            disp = disp.rsplit(".", 1)[0]
        return disp.replace(".", "-")
    if mkt == "hk":
        return disp.lstrip("0").zfill(4) + ".HK"
    if mkt == "sh":
        return disp + ".SS"
    if mkt == "sz":
        return disp + ".SZ"
    return None


def _fetch_yahoo_daily(symbol, n=12):
    """美股复用 factor_engine 的 Yahoo 日K(与因子选股同源); 港股用本地解析。"""
    tick = _us_ticker(symbol)
    if tick and factor_engine is not None:
        try:
            bars = factor_engine.fetch_us_bars(tick, max(int(n), 12))
            if bars:
                return [{"date": b[0], "open": b[1], "close": b[2],
                         "high": b[3], "low": b[4], "volume": b[5]}
                        for b in bars]
        except Exception:
            pass
    if (not _host_reachable(YAHOO_DAILY_URL)
            or not _intl_ok("yahoo") or not _overseas_ok("yahoo")):
        return []
    sym = _yahoo_symbol(symbol)
    if not sym:
        return []
    try:
        raw = _http(YAHOO_DAILY_URL.format(sym=sym), UA, timeout=8)
        data = json.loads(raw.decode("utf-8", "replace"))
        res = (data.get("chart") or {}).get("result") or []
        if not res:
            return []
        meta = res[0].get("meta") or {}
        ts = res[0].get("timestamp") or []
        quote = (res[0].get("indicators", {}).get("quote") or [{}])[0]
        closes = quote.get("close") or []
        opens = quote.get("open") or []
        highs = quote.get("high") or []
        lows = quote.get("low") or []
        vols = quote.get("volume") or []
        offset = int(meta.get("gmtoffset") or 0)
        bars = []
        for i, t in enumerate(ts):
            c = closes[i] if i < len(closes) else None
            if c is None:
                continue
            bars.append({
                "date": time.strftime("%Y-%m-%d", time.gmtime(float(t) + offset)),
                "open": opens[i] if i < len(opens) else None,
                "close": c,
                "high": highs[i] if i < len(highs) else None,
                "low": lows[i] if i < len(lows) else None,
                "volume": vols[i] if i < len(vols) else 0,
            })
        return bars[-n:]
    except Exception:
        return []


def _fetch_yahoo_minutes(code, n=60):
    """港股/美股逐笔不可得时的 1 分钟分时兜底。"""
    if (not _host_reachable(YAHOO_CHART_URL)
            or not _intl_ok("yahoo") or not _overseas_ok("yahoo")):
        return []
    sym = _yahoo_symbol(code)
    if not sym:
        return []
    try:
        raw = _http(YAHOO_CHART_URL.format(sym=sym), UA, timeout=8)
        data = json.loads(raw.decode("utf-8", "replace"))
        res = (data.get("chart") or {}).get("result") or []
        if not res:
            return []
        meta = res[0].get("meta") or {}
        ts = res[0].get("timestamp") or []
        quote = (res[0].get("indicators", {}).get("quote") or [{}])[0]
        closes = quote.get("close") or []
        vols = quote.get("volume") or []
        offset = int(meta.get("gmtoffset") or 0)
        rows = []
        prev = None
        for t, price, vol in zip(ts, closes, vols):
            if price is None:
                continue
            direction = ("买" if prev is not None and price > prev
                         else ("卖" if prev is not None and price < prev else "中性"))
            rows.append({
                "time": time.strftime("%H:%M", time.gmtime(float(t) + offset)),
                "price": float(price),
                "volume": vol,
                "direction": direction,
            })
            prev = price
        return rows[-n:]
    except Exception:
        return []


# ---------------------------------------------------------------------------
# 选股数据源: 新浪 A股全市场列表 + 腾讯量比
# ---------------------------------------------------------------------------

def sina_fetch_page(page=1, num=100):
    """新浪 A股全市场列表, 按涨跌幅降序, 返回 list[dict]。"""
    url = SINA_LIST_URL.format(page=page, num=num)
    raw = _http(url, SINA_HDR, timeout=12).decode("utf-8", "replace")
    return json.loads(raw)


def sina_fetch_candidates(min_gain):
    """并行分批翻页抓取 A股中涨幅 >= min_gain 的所有原始行(每批 10 页并发)。"""
    out = []
    for start in range(1, 61, 10):
        def fetch(pg):
            try:
                return sina_fetch_page(pg, 100)
            except Exception:
                return []
        with ThreadPoolExecutor(max_workers=10) as ex:
            batch = list(ex.map(fetch, range(start, start + 10)))
        stop = False
        for arr in batch:
            if not arr:
                stop = True
                break
            for r in arr:
                cp = to_float(r.get("changepercent"))
                if cp is None:
                    continue
                if cp < min_gain:
                    stop = True
                    break
                out.append(r)
            if stop:
                break
        if stop:
            break
    return out


def fetch_screen_universe(market="a", f_min=0.0, limit=800):
    """选股器统一股票池: a=A股, us=美股, etf=A股ETF。"""
    out = []
    if market == "us":
        if factor_engine is None:
            raise RuntimeError("factor_engine.py 不可用")
        # 与因子选股共用 Yahoo 美股池/报价, 两边价格与涨跌幅一致
        rows = factor_engine.fetch_us_universe(limit)
        for r in rows:
            out.append({
                "symbol": r.get("symbol"), "code": r.get("code"),
                "name": r.get("name") or r.get("code"),
                "price": r.get("price"),
                "pct": r.get("pct"),
                "amount": r.get("amount"),
                "volume": r.get("volume"),
                "turnover": r.get("hs"),
                "lb": r.get("lb"),
                "high": r.get("high"),
                "low": r.get("low"),
                "open": r.get("open"),
                "market_cap": r.get("market_cap"),
                "pe": r.get("pe"), "pb": r.get("pb"),
                "prev_close": r.get("prev_close"),
                "industry": r.get("industry") or r.get("sector") or "—",
                "market": "us",
            })
        return out
    if market == "etf":
        if factor_engine is None:
            raise RuntimeError("factor_engine.py 不可用")
        rows = factor_engine.fetch_sina_universe(
            limit, exclude_st=False, node="etf_hq_fund", market="etf")
        for r in rows:
            out.append({
                "symbol": r.get("symbol"), "code": r.get("code"),
                "name": r.get("name") or r.get("code"),
                "price": r.get("price"), "pct": r.get("pct"),
                "amount": r.get("amount"), "volume": r.get("volume"),
                "turnover": r.get("turnover"), "high": r.get("high"),
                "low": r.get("low"), "open": r.get("open"),
                "market_cap": None, "industry": "ETF", "market": "etf",
            })
        return out
    raw = sina_fetch_candidates(f_min)
    for r in raw:
        out.append({
            "symbol": r.get("symbol"), "code": r.get("code"),
            "name": r.get("name") or r.get("code"),
            "price": to_float(r.get("trade")), "pct": to_float(r.get("changepercent")),
            "amount": to_float(r.get("amount"), 0), "volume": to_float(r.get("volume"), 0),
            "turnover": to_float(r.get("turnoverratio")),
            "high": to_float(r.get("high")), "low": to_float(r.get("low")),
            "open": to_float(r.get("open")),
            "market_cap": None, "industry": "", "market": "a",
        })
    return out


_A_METRICS_CACHE = {}
_A_METRICS_TTL = 60.0


def fetch_a_metrics(symbol):
    """腾讯 A股单只: 返回 (量比, 换手率)。带 60s TTL 缓存。symbol 形如 sh600519。"""
    now = time.time()
    hit = _A_METRICS_CACHE.get(symbol)
    if hit and now - hit[0] < _A_METRICS_TTL:
        return hit[1], hit[2]
    try:
        raw = _http("https://qt.gtimg.cn/q=" + symbol, UA).decode("gbk", "replace")
        p = raw.split('"')[1].split("~")
        lb = to_float(p[49]) if len(p) > 49 else None
        hs = to_float(p[38]) if len(p) > 38 else None
        _A_METRICS_CACHE[symbol] = (now, lb, hs)
        return lb, hs
    except Exception:
        return None, None


# ---------------------------------------------------------------------------
# 历史日K(腾讯 ifzq): 当日 vs 昨日 涨幅对比 + 时间序列因子
# ---------------------------------------------------------------------------

KLINE_URL = "https://web.ifzq.gtimg.cn/appstock/app/fqkline/get?param={sym},day,,,{n},qfq"
SINA_KLINE_URL = ("https://money.finance.sina.com.cn/quotes_service/api/json_v2.php/"
                  "CN_MarketData.getKLineData?symbol={sym}&scale=240&ma=no&datalen={n}")
KLINE_HDR = {"User-Agent": UA["User-Agent"], "Referer": "https://gu.qq.com/"}

_KLINE_CACHE = {}       # symbol -> 昨日指标 dict(当日有效)
_KLINE_CACHE_FILE = os.path.join(os.path.dirname(os.path.abspath(__file__)), "kline_cache.json")
_KLINE_FAIL_TS = {}     # symbol -> 上次失败时间(负缓存, 避免反复重试打爆接口)
_KLINE_FAIL_TTL = 600.0
_KLINE_TENCENT_OFF_UNTIL = 0.0
_KLINE_TENCENT_FAILS = 0
_KLINE_TEN_LOCK = threading.Lock()


def _kline_today_ref(mkt):
    """日K最后一根是否为「当日」bar 的参照日期。
    美股交易日比北京日期晚约1天(收盘在北京凌晨), 用本地日期-1天作参照。"""
    if mkt == "us":
        return time.strftime("%Y-%m-%d", time.localtime(time.time() - 86400))
    if mkt == "cr":
        return time.strftime("%Y-%m-%d", time.gmtime())
    return time.strftime("%Y-%m-%d")


def _fetch_sina_daily_kline(symbol, n=12):
    """腾讯限流时的日K回退(不复权, 成交量统一成手)。"""
    try:
        raw = _http(SINA_KLINE_URL.format(sym=symbol, n=n), SINA_HDR, timeout=8)
        arr = json.loads(raw.decode("utf-8", "replace"))
        if not isinstance(arr, list):
            return []
        out = []
        for x in arr:
            if not isinstance(x, dict):
                continue
            date = str(x.get("day") or "")[:10]
            o = to_float(x.get("open"))
            c = to_float(x.get("close"))
            h = to_float(x.get("high"))
            l = to_float(x.get("low"))
            v = to_float(x.get("volume"), 0)
            if date and None not in (o, c, h, l):
                out.append({"date": date, "open": o, "close": c, "high": h,
                            "low": l, "volume": (v or 0) / 100.0})
        return out
    except Exception:
        return []


def fetch_daily_kline(symbol, n=12):
    """日K(腾讯前复权, 失败回退新浪): 返回 list[dict(date,open,close,high,low,volume)]
    旧->新, 失败返回 []。A股/港股直接用 sh/sz/bj/hk 前缀代码;
    美股优先 Yahoo(与因子选股同源), 再回退腾讯/Nasdaq; 加密用 crBTCUSDT。"""
    if symbol.startswith("cr"):
        return fetch_crypto_bars(symbol[2:], n)
    if symbol.startswith("us"):
        bars = _fetch_yahoo_daily(symbol, n)
        if bars:
            return bars
    global _KLINE_TENCENT_OFF_UNTIL, _KLINE_TENCENT_FAILS
    if time.time() >= _KLINE_TENCENT_OFF_UNTIL:
        try:
            qsym = _us_tencent_code(symbol)
            raw = _http(KLINE_URL.format(sym=qsym, n=n), KLINE_HDR, timeout=3).decode("utf-8", "replace")
            node = (json.loads(raw).get("data") or {}).get(qsym) or {}
            arr = node.get("qfqday") or node.get("day") or []
            out = []
            for b in arr:
                if isinstance(b, (list, tuple)) and len(b) >= 6:
                    out.append({"date": str(b[0]), "open": to_float(b[1]), "close": to_float(b[2]),
                                "high": to_float(b[3]), "low": to_float(b[4]), "volume": to_float(b[5], 0)})
            if out:
                with _KLINE_TEN_LOCK:
                    _KLINE_TENCENT_FAILS = 0
                return out
        except Exception:
            pass
        with _KLINE_TEN_LOCK:
            _KLINE_TENCENT_FAILS += 1
            if _KLINE_TENCENT_FAILS >= 3:
                _KLINE_TENCENT_OFF_UNTIL = time.time() + 600
    bars = _fetch_sina_daily_kline(symbol, n)
    if bars:
        return bars
    if symbol.startswith("us"):
        tick = _us_ticker(symbol)
        if tick:
            bars = fetch_nasdaq_daily(tick, n)
            if bars:
                return bars
    return []


def derive_prev_metrics(bars, today_ref, us=False):
    """从日K(旧->新)提取「昨日」截面指标(当日未定型 bar 不参与):
    p=昨日涨幅%  s=截至昨日连涨天数  vr=昨日量/前5日均量。数据不足返回 None。"""
    hist = [b for b in bars if b.get("close")]
    if us:
        # Yahoo 美股日线包含盘中未收盘 bar: 只保留 <= 参照日 的已完成交易日
        hist = [b for b in hist if b["date"][:10] <= today_ref]
    elif hist and hist[-1]["date"][:10] == today_ref:
        hist = hist[:-1]                      # 剔除当日(盘中未定型)bar
    if len(hist) < 2:
        return None
    prev, prev2 = hist[-1], hist[-2]
    m = {"p": round((prev["close"] / prev2["close"] - 1) * 100, 2)}
    streak = 0                                # 截至昨日的连涨天数
    for i in range(len(hist) - 1, 0, -1):
        if hist[i]["close"] > hist[i - 1]["close"]:
            streak += 1
        else:
            break
    m["s"] = streak
    vols = [b["volume"] for b in hist[-6:-1] if b.get("volume")]
    if len(vols) == 5 and prev.get("volume"):
        avg = sum(vols) / 5.0
        if avg > 0:
            m["vr"] = round(prev["volume"] / avg, 2)
    return m


def fetch_prev_metrics(symbol):
    """带缓存的昨日指标(当日有效, 内存+磁盘), 失败负缓存 10 分钟。
    symbol 形如 sh600519 / hk00700 / usAAPL.OQ。"""
    if symbol in _KLINE_CACHE:
        return _KLINE_CACHE[symbol]
    fail = _KLINE_FAIL_TS.get(symbol)
    if fail and time.time() - fail < _KLINE_FAIL_TTL:
        return None
    m = derive_prev_metrics(fetch_daily_kline(symbol), _kline_today_ref(symbol[:2]),
                            us=symbol.startswith("us"))
    if m is None:
        _KLINE_FAIL_TS[symbol] = time.time()
        return None
    _KLINE_CACHE[symbol] = m
    return m


def _load_kline_cache():
    try:
        with open(_KLINE_CACHE_FILE, "r", encoding="utf-8") as f:
            data = json.load(f)
        if data.get("_saved") == time.strftime("%Y-%m-%d"):
            for k, v in data.items():
                if not k.startswith("_") and isinstance(v, dict):
                    _KLINE_CACHE[k] = v
    except Exception:
        pass


def _save_kline_cache():
    try:
        data = {"_saved": time.strftime("%Y-%m-%d")}
        data.update(_KLINE_CACHE)
        with open(_KLINE_CACHE_FILE, "w", encoding="utf-8") as f:
            json.dump(data, f, ensure_ascii=False)
    except Exception:
        pass


_INDUSTRY_CACHE = {}
_INDUSTRY_CACHE_FILE = os.path.join(os.path.dirname(os.path.abspath(__file__)), "industry_cache.json")


def _load_industry_cache():
    try:
        with open(_INDUSTRY_CACHE_FILE, "r", encoding="utf-8") as f:
            _INDUSTRY_CACHE.update(json.load(f))
    except Exception:
        pass


def _save_industry_cache():
    try:
        with open(_INDUSTRY_CACHE_FILE, "w", encoding="utf-8") as f:
            json.dump(_INDUSTRY_CACHE, f, ensure_ascii=False)
    except Exception:
        pass


def fetch_industry(symbol):
    """行业(申万二级): 先查内存缓存, 未命中走东财 F10 接口并缓存。symbol 形如 sh600519。"""
    if symbol in _INDUSTRY_CACHE:
        return _INDUSTRY_CACHE[symbol]
    result = "—"
    try:
        url = ("https://emweb.securities.eastmoney.com/PC_HSF10/CompanySurvey/PageAjax"
               f"?code={symbol.upper()}")
        hdr = {"User-Agent": UA["User-Agent"], "Referer": "https://emweb.securities.eastmoney.com/"}
        data = json.loads(_http(url, hdr, timeout=6).decode("utf-8", "replace"))
        jbzl = data.get("jbzl") or []
        if jbzl:
            em = jbzl[0].get("EM2016") or ""
            parts = [p for p in em.split("-") if p]
            result = parts[1] if len(parts) >= 2 else (parts[0] if parts else "—")
    except Exception:
        pass
    if result != "—":
        _INDUSTRY_CACHE[symbol] = result
    return result


# ---------------------------------------------------------------------------
# 开盘倾向: 横截面多因子打分 (量化选股)
# ---------------------------------------------------------------------------
# 把原「启发式单指标」升级为「多因子横截面打分」:
#   1) 每个因子在候选集内做分位排名(0~1), 天然稳健、抗离群值、量纲统一
#   2) 因子按先验权重线性合成, 权重和为 1, 映射到 0~100
#   3) 标签用固定阈值(60/40), 约对应前/后 15~20%「高开」/「低开」
# 因子分三类:
#   - 时间序列因子(当日 vs 昨日, 来自日K): 动量加速度(涨幅差)、连涨天数、昨日量能
#   - 当日截面因子(实时快照): 尾盘强度、量比、换手、成交额、日内动量
#   - 消息面因子(近24h资讯): 利好/利空条数差
# 说明: 权重为「先验假设」。本工具离线、无历史数据, 未做 IC/回测估计;
#       仅作强弱排序参考, 不构成任何预测保证。
# ---------------------------------------------------------------------------

# 因子权重(和为 1): 涨幅加速 > 消息面/尾盘强度 > 量比/连涨/昨日量能/换手 > 成交额/当日动量
FACTOR_WEIGHTS = {
    "accel":          0.20,   # 动量加速度(核心): 今日涨幅 - 昨日涨幅, >0 为动能增强
    "news":           0.15,   # 24h消息面: 利好条数 - 利空条数(关键词启发式)
    "close_position": 0.15,   # 收盘位置(尾盘强度): (收盘-最低)/(最高-最低)
    "volume_ratio":   0.10,   # 量比(动能): 当日量能相对 5 日均量的放大
    "up_streak":      0.10,   # 连涨天数(含今日): 趋势持续性
    "vol_prev_ratio": 0.10,   # 昨日量/前5日均量: 前日资金介入度
    "turnover":       0.10,   # 换手率(关注度/流动性)
    "amount":         0.05,   # 成交额(资金规模, 取对数)
    "momentum":       0.05,   # 当日涨跌幅(筛选区间窄, 区分度低)
}

# 开盘倾向标签阈值(0~100 分)。
# 9 因子合成分位加权的分布集中在中位附近(约50±10), 60/40 约对应前/后 15~20%。
BIAS_HIGH = 60
BIAS_LOW = 40

# 买入候选信号阈值(0~4 项共振)
SIGNAL_STRONG = 4          # 4 项全共振: 强候选(深黄底)
SIGNAL_CAND = 3            # >=3 项: 候选(浅黄底)


def buy_signal(row):
    """买入候选信号: 统计 4 项多头条件的共振数(0~4)。
    条件: 开盘倾向>=60 / 涨幅差>0(今日强于昨日) / 连涨>=2天(含今日) / 24h无利空消息。
    缺失数据按不满足处理(保守)。仅作筛选参考, 不构成投资建议。"""
    checks = (
        row.get("bias") is not None and row["bias"] >= BIAS_HIGH,
        row.get("delta") is not None and row["delta"] > 0,
        row.get("streak") is not None and row["streak"] >= 2,
        row.get("news_score") is not None and row["news_score"] >= 0,
    )
    return sum(1 for ok in checks if ok)


def _f_close_position(row):
    """收盘位置: (收盘-最低)/(最高-最低), 越接近 1 越强(尾盘强势)。"""
    high, low, price = row.get("high"), row.get("low"), row.get("price")
    if high is None or low is None or price is None or high <= low:
        return None
    return (price - low) / (high - low)


def _f_momentum(row):
    return row.get("pct")


def _f_accel(row):
    """动量加速度: 今日涨幅 - 昨日涨幅(百分点)。>0 = 涨幅扩大或跌幅收窄(动能增强)。"""
    return row.get("delta")


def _f_up_streak(row):
    """连涨天数(含今日): 趋势持续性。今日下跌则为 0。"""
    return row.get("streak")


def _f_vol_prev_ratio(row):
    """昨日量/前5日均量: 今日启动前一日是否已有资金放量介入。"""
    return row.get("vr")


def _f_news(row):
    """24h消息面得分: 利好条数 - 利空条数(关键词启发式)。>0 = 近24h偏利好。"""
    return row.get("news_score")


def _f_volume_ratio(row):
    return row.get("lb")


def _f_turnover(row):
    return row.get("hs")


def _f_amount(row):
    """成交额取对数: 金额重尾分布, 对数压缩后更接近正态, 利于横截面比较。"""
    a = row.get("amount")
    if a is None or a <= 0:
        return None
    return math.log10(a)


_FACTOR_EXTRACTORS = {
    "accel": _f_accel,
    "up_streak": _f_up_streak,
    "vol_prev_ratio": _f_vol_prev_ratio,
    "news": _f_news,
    "close_position": _f_close_position,
    "volume_ratio": _f_volume_ratio,
    "turnover": _f_turnover,
    "momentum": _f_momentum,
    "amount": _f_amount,
}


def _percentile_rank(values):
    """横截面分位排名(平均秩法), 返回 [0,1]; 缺失值(None)返回 None。
    稳健: 不依赖原始量纲, 抗极端值。"""
    n = len(values)
    ranked = [None] * n
    pairs = sorted(((i, v) for i, v in enumerate(values) if v is not None),
                   key=lambda t: t[1])
    m = len(pairs)
    if m == 0:
        return ranked
    j = 0
    while j < m:
        k = j
        while k < m and pairs[k][1] == pairs[j][1]:
            k += 1
        avg = (j + k - 1) / (2.0 * (m - 1)) if m > 1 else 0.5
        for idx, _ in pairs[j:k]:
            ranked[idx] = avg
        j = k
    return ranked


def open_bias_composite(rows, weights=FACTOR_WEIGHTS):
    """对候选集做横截面多因子合成, 就地写入每行的 bias(0~100) 与 bias_label。

    流程: 提取原始因子 -> 分位排名 -> 加权求和 -> 缩放 0~100 -> 阈值标签。
    缺失因子按中性(0.5)处理, 不奖励也不惩罚, 属保守做法。
    """
    if not rows:
        return rows
    raw = {name: [_FACTOR_EXTRACTORS[name](r) for r in rows] for name in weights}
    ranks = {name: _percentile_rank(raw[name]) for name in weights}
    for i, r in enumerate(rows):
        score = 0.0
        for name, w in weights.items():
            rk = ranks[name][i]
            if rk is None:
                rk = 0.5
            score += w * rk
        score = round(score * 100)
        r["bias"] = score
        r["bias_label"] = "高开" if score >= BIAS_HIGH else ("低开" if score <= BIAS_LOW else "中性")
    return rows


def detail_url(mkt, disp):
    """详情页: 美股雪球, A股/港股腾讯, 加密货币 Binance。"""
    if mkt == "us":
        return f"https://xueqiu.com/S/{disp}"
    if mkt == "hk":
        return f"https://gu.qq.com/hk{disp}"
    if mkt == "cr":
        return f"https://www.binance.com/en/trade/{disp}USDT"
    return f"https://gu.qq.com/{mkt}{disp}"   # sh / sz / bj


# ---------------------------------------------------------------------------
# 综合评估: 基本面 + 消息面 + 技术面 + 买入区间
# ---------------------------------------------------------------------------

def is_etf(raw):
    c = classify_symbol(raw)
    if not c or c[2] not in ("sh", "sz"):
        return False
    code = c[1]
    return code.startswith(("15", "16", "18", "50", "51", "52", "56", "58"))


def fetch_tencent_fundamentals(tcode):
    """腾讯长格式里的估值字段; 失败返回空。"""
    if not tcode or tcode.startswith("cr"):
        return {}
    try:
        raw = _http("https://qt.gtimg.cn/q=" + tcode, UA, timeout=6).decode("gbk", "replace")
        p = raw.split('"')[1].split("~")
        if len(p) < 50:
            return {}
        us = tcode.startswith("us")
        pe = _raw_float(p[39])
        pb = None if us else _raw_float(p[46] if not tcode.startswith("hk") else p[58])
        mktcap = _raw_float(p[45]) or _raw_float(p[44])
        turnover = _raw_float(p[38])
        h52 = _raw_float(p[48] if us else p[47])
        l52 = _raw_float(p[49] if us else p[48])
        return {"pe": pe if pe and pe > 0 else None,
                "pb": pb if pb and pb > 0 else None,
                "mktcap": mktcap, "turnover": turnover,
                "high52": h52, "low52": l52}
    except Exception:
        return {}


def _eval_sma(vals, n):
    return sum(vals[-n:]) / n if len(vals) >= n else None


def _eval_ema(vals, n):
    if not vals:
        return []
    k = 2.0 / (n + 1.0)
    out = [vals[0]]
    for x in vals[1:]:
        out.append(out[-1] + (x - out[-1]) * k)
    return out


def _eval_rsi(closes, n=14):
    if len(closes) <= n:
        return None
    gains, losses = [], []
    for i in range(1, len(closes)):
        d = closes[i] - closes[i - 1]
        gains.append(max(d, 0.0))
        losses.append(max(-d, 0.0))
    ag = sum(gains[-n:]) / n
    al = sum(losses[-n:]) / n
    if al <= 0:
        return 100.0
    return 100.0 - 100.0 / (1.0 + ag / al)


def _eval_atr(highs, lows, closes, n=14):
    if len(closes) <= n:
        return None
    trs = []
    for i in range(1, len(closes)):
        trs.append(max(highs[i] - lows[i],
                       abs(highs[i] - closes[i - 1]),
                       abs(lows[i] - closes[i - 1])))
    return sum(trs[-n:]) / n


def technical_snapshot(bars, price=None):
    bars = [b for b in bars if b.get("close") is not None]
    if len(bars) < 25:
        return {"bars": len(bars)}
    closes = [b["close"] for b in bars]
    highs = [b.get("high") or b["close"] for b in bars]
    lows = [b.get("low") or b["close"] for b in bars]
    vols = [b.get("volume") or 0 for b in bars]
    price = price or closes[-1]
    ma5, ma10 = _eval_sma(closes, 5), _eval_sma(closes, 10)
    ma20, ma60 = _eval_sma(closes, 20), _eval_sma(closes, 60)
    e12, e26 = _eval_ema(closes, 12), _eval_ema(closes, 26)
    dif = [a - b for a, b in zip(e12, e26)]
    dea = _eval_ema(dif, 9)
    macd_hist = (dif[-1] - dea[-1]) if dif and dea else None
    rsi = _eval_rsi(closes, 14)
    atr = _eval_atr(highs, lows, closes, 14)
    std20 = None
    if len(closes) >= 20:
        m = sum(closes[-20:]) / 20.0
        std20 = math.sqrt(sum((x - m) ** 2 for x in closes[-20:]) / 20.0)
    boll_up = (ma20 + 2 * std20) if (ma20 is not None and std20 is not None) else None
    boll_low = (ma20 - 2 * std20) if (ma20 is not None and std20 is not None) else None
    ret5 = closes[-1] / closes[-6] - 1 if len(closes) >= 6 else None
    ret20 = closes[-1] / closes[-21] - 1 if len(closes) >= 21 else None
    high20, low20 = max(highs[-20:]), min(lows[-20:])
    high60 = max(highs[-60:]) if len(highs) >= 60 else high20
    low60 = min(lows[-60:]) if len(lows) >= 60 else low20
    vol20 = None
    if len(closes) >= 21:
        lr = [math.log(closes[i] / closes[i - 1]) for i in range(len(closes) - 20, len(closes))]
        m = sum(lr) / len(lr)
        vol20 = math.sqrt(sum((x - m) ** 2 for x in lr) / (len(lr) - 1)) * math.sqrt(252)
    close_pos20 = ((closes[-1] - low20) / (high20 - low20)) if high20 > low20 else 0.5
    trend = "震荡"
    if ma20 is not None and ma60 is not None:
        if price > ma20 > ma60:
            trend = "多头"
        elif price < ma20 < ma60:
            trend = "空头"
    atr = atr or price * 0.02
    if price > high20 * 1.01:
        style = "突破回踩"
        buy_low = max(high20 - 0.3 * atr, price - 1.0 * atr)
        buy_high = min(price, max(high20 + 0.2 * atr, buy_low + 0.4 * atr))
    elif trend == "多头":
        style = "趋势回调"
        buy_low = max(low20, price - 1.5 * atr, (ma20 or low20) - 0.3 * atr)
        buy_high = min(price, max((ma20 or price) + 0.5 * atr, buy_low + 0.6 * atr))
    elif trend == "空头":
        style = "等待企稳"
        buy_low = max(low20, price - 1.5 * atr)
        buy_high = min(price, max(buy_low + 0.5 * atr, (ma20 or price) - 1.0 * atr))
    else:
        style = "区间低吸"
        buy_low = max(low20, price - 1.2 * atr, (ma20 or price) - 0.8 * atr)
        buy_high = min(price, max(buy_low + 0.6 * atr, (ma20 or price) - 0.2 * atr))
    if buy_high <= buy_low:
        buy_high = min(price, buy_low * 1.01)
    if buy_high <= buy_low:
        buy_low, buy_high = price * 0.98, price
    stop = buy_low - 0.8 * atr
    resistance = high20 if high20 > price else high60
    target = max(resistance, buy_high + 2 * atr)
    return {
        "bars": len(bars), "price": price,
        "ma5": ma5, "ma10": ma10, "ma20": ma20, "ma60": ma60,
        "rsi": rsi, "atr": atr, "macd_hist": macd_hist,
        "boll_up": boll_up, "boll_low": boll_low,
        "ret5": ret5, "ret20": ret20, "vol20": vol20,
        "high20": high20, "low20": low20, "high60": high60, "low60": low60,
        "close_pos20": close_pos20, "trend": trend, "style": style,
        "buy_low": buy_low, "buy_high": buy_high, "stop": stop, "target": target,
    }


def _eval_price(v, mkt, etf):
    if v is None:
        return "--"
    if mkt == "cr":
        return fmt_crypto_price(v)
    if etf:
        return f"{v:.3f}"
    return fmt_price(v)


def collect_evaluation(code, quote=None, factor_row=None):
    c = classify_symbol(code)
    if not c:
        return {"error": "无法识别该代码"}
    tcode, disp, mkt = c
    etf = is_etf(code)
    if quote is None:
        if mkt == "cr":
            q, _ = fetch_crypto_quotes([code])
        else:
            q, _ = fetch_quotes_auto([(code, sina_code(code), tcode)])
        quote = q.get(code)
    bars = fetch_daily_kline(tcode, 120)
    asof = bars[-1].get("date") if bars else ""
    tech = technical_snapshot(bars, price=(quote or {}).get("price"))
    fund = fetch_tencent_fundamentals(tcode)
    ynews = []
    if mkt == "cr":
        fund = {"kind": "crypto"}
    else:
        fund["kind"] = "etf" if etf else "stock"
        if mkt == "us":
            tick = _us_ticker(tcode) or disp
            with ThreadPoolExecutor(max_workers=3) as ex:
                f_nas = ex.submit(fetch_nasdaq_summary, tick)
                f_sec = ex.submit(fetch_sec_fundamentals, tick)
                f_news = ex.submit(fetch_yahoo_news, tick, 6)
                nas = f_nas.result()
                sec = f_sec.result()
                ynews = f_news.result()
            if nas:
                if nas.get("mktcap"):
                    fund["mktcap"] = nas["mktcap"] / 1e8
                for k in ("sector", "industry", "high52", "low52",
                          "avg_volume", "one_year_target", "dividend", "yield"):
                    if nas.get(k) is not None:
                        fund[k] = nas[k]
            if sec:
                fund.update({k: v for k, v in sec.items() if v is not None})
            pr = (quote or {}).get("price")
            if pr and sec.get("eps") and fund.get("pe") is None:
                fund["pe"] = pr / sec["eps"]
            if pr and sec.get("equity") and sec.get("shares"):
                bvps = sec["equity"] / sec["shares"]
                if bvps > 0 and fund.get("pb") is None:
                    fund["pb"] = pr / bvps
            # 国内直连回退: 东财美股详情补 PB/市值/换手/52周/行业
            emf = fetch_em_us_fundamentals(tick)
            for k in ("pb", "mktcap", "turnover", "high52", "low52",
                      "prev_close", "industry"):
                if emf.get(k) is not None and fund.get(k) is None:
                    fund[k] = emf[k]
            if emf.get("name") and not (quote or {}).get("name"):
                fund["name"] = emf["name"]
    industry = ""
    if mkt in ("sh", "sz", "bj") and not etf:
        try:
            industry = fetch_industry(tcode)
        except Exception:
            industry = ""
    if not industry:
        industry = fund.get("industry") or fund.get("sector") or ""
    news, nstats = [], {"n_pos": 0, "n_neg": 0}
    if mkt in ("sh", "sz", "bj", "hk", "us"):
        try:
            em_news, _em_stats = fetch_stock_news(mkt, disp, (quote or {}).get("qt_code", ""))
        except Exception:
            em_news = []
        combined = []
        seen = set()
        for it in (ynews + em_news):
            title = str(it.get("title") or "")
            if title and title not in seen:
                seen.add(title)
                combined.append(it)
        combined.sort(key=lambda x: x.get("time") or "", reverse=True)
        news = combined[:12]
        nstats = {"n_pos": sum(1 for x in news if x.get("impact") == "利好"),
                  "n_neg": sum(1 for x in news if x.get("impact") == "利空")}
    price = (quote or {}).get("price") or tech.get("price")
    score = 50.0
    if tech.get("ma20") is not None:
        if price and price > tech["ma20"]:
            score += 8
        if tech.get("ma60") is not None and tech["ma20"] > tech["ma60"]:
            score += 8
        if tech.get("ma5") and tech["ma20"] and tech["ma5"] > tech["ma20"]:
            score += 4
        if tech.get("macd_hist") is not None and tech["macd_hist"] > 0:
            score += 6
        if tech.get("ret20") is not None and tech["ret20"] > 0:
            score += 4
        if tech.get("ret5") is not None and tech["ret5"] > 0:
            score += 3
        rsi = tech.get("rsi")
        if rsi is not None:
            if 45 <= rsi <= 70:
                score += 4
            elif rsi > 75:
                score -= 6
            elif rsi < 30:
                score += 2
        vol = tech.get("vol20")
        if vol is not None:
            if vol < 0.4:
                score += 4
            elif vol > 0.8:
                score -= 5
        if tech.get("close_pos20", 0.5) > 0.5:
            score += 3
    pe, pb = fund.get("pe"), fund.get("pb")
    if pe is not None:
        if pe < 30:
            score += 2
        elif pe > 80:
            score -= 3
    if pb is not None:
        if pb < 5:
            score += 1
        elif pb > 10:
            score -= 3
    diff = nstats.get("n_pos", 0) - nstats.get("n_neg", 0)
    score += max(-4, min(4, diff))
    if factor_row:
        adv = factor_row.get("advice")
        if adv == "强候选":
            score += 3
        elif adv == "候选":
            score += 2
        elif adv == "观察":
            score -= 2
        elif adv == "回避":
            score -= 6
    score = max(0.0, min(95.0, score))
    if score >= 75:
        label = "偏多"
    elif score >= 60:
        label = "中性偏多"
    elif score >= 45:
        label = "中性"
    elif score >= 35:
        label = "偏弱"
    else:
        label = "回避"
    action = "可在区间内分批；跌破止损放弃"
    if tech.get("trend") == "空头" or score < 35:
        action = "暂不买入，等待企稳或放量突破"
    if factor_row and factor_row.get("advice") == "回避":
        action = "因子标注回避，暂不买入"
    zone_notes = []
    if tech.get("buy_low") is not None:
        if diff < 0:
            zone_notes.append("消息面偏空")
        if pe is not None and pe > 80:
            zone_notes.append("PE偏高")
        if pb is not None and pb > 10:
            zone_notes.append("PB偏高")
        if score < 45:
            zone_notes.append("综合评分偏弱")
        if zone_notes:
            shift = 0.3 * (tech.get("atr") or 0)
            low = max(tech.get("low20") or 0, tech["buy_low"] - shift)
            high = max(low * 1.005, tech["buy_high"] - shift)
            high = min(high, price) if price else high
            tech["buy_low"], tech["buy_high"] = low, high
            tech["stop"] = low - 0.8 * (tech.get("atr") or 0)
        elif diff > 0 and score >= 60:
            tech["buy_high"] = min(price, tech["buy_high"] + 0.1 * (tech.get("atr") or 0))
            zone_notes.append("消息面偏正，区间略上移")
        tech["zone_note"] = "；".join(zone_notes)
    return {
        "error": None, "code": code, "tcode": tcode, "disp": disp, "mkt": mkt,
        "etf": etf, "name": (quote or {}).get("name") or disp,
        "quote": quote or {}, "tech": tech, "fund": fund, "asof": asof,
        "news": news, "nstats": nstats, "factor": factor_row,
        "industry": industry,
        "score": round(score), "label": label, "action": action,
    }


def format_evaluation(ev):
    if ev.get("error"):
        return [("warn", ev["error"])]
    q, t, f = ev["quote"], ev["tech"], ev["fund"]
    mkt, etf = ev["mkt"], ev["etf"]
    pf = lambda v: _eval_price(v, mkt, etf)
    market_label = "加密货币" if mkt == "cr" else ("ETF/LOF" if etf else MARKET_LABEL.get(mkt, mkt))
    lines = []
    add = lambda tag, text: lines.append((tag, text))
    qpct = q.get("pct")
    add("h", f"{ev['name']}  {ev['disp']}  ·  {market_label}")
    add("muted", f"现价 {pf(q.get('price'))}  涨跌 "
                 f"{('--' if qpct is None else f'{qpct:+.2f}%')}  ·  "
                 f"数据日 {ev.get('asof') or '--'}")
    add("h", "综合结论")
    add("buy" if ev["score"] >= 60 else "sell" if ev["score"] < 35 else "warn",
        f"综合评分 {ev['score']}/100 · {ev['label']}")
    if ev.get("factor"):
        fr = ev["factor"]
        add("muted", f"因子标注：{fr.get('advice') or '—'}  "
                     f"（得分 {fr.get('score'):.1f}，{fr.get('advice_reason') or ''}）")
    if t.get("buy_low") is not None:
        low, high = t["buy_low"], t["buy_high"]
        p = q.get("price")
        pull = ((low / p - 1) * 100) if p else None
        add("buy", f"建议买入区间：{pf(low)} ~ {pf(high)}"
                    + (f"（现价下方 {pull:+.1f}%）" if pull is not None else ""))
        add("muted", f"止损参考 {pf(t['stop'])}  ·  目标参考 {pf(t['target'])}  ·  形态：{t['style']}")
        if t.get("zone_note"):
            add("warn", f"区间调整依据：{t['zone_note']}")
    add("buy" if ev["score"] >= 60 else "warn", f"操作建议：{ev['action']}")

    add("h", "基本面")
    if f.get("kind") == "crypto":
        add("muted", f"24h成交额 {fmt_amount(q.get('amount'))} · 24h量 {fmt_vol(q.get('volume'))}")
        add("muted", "加密资产无公司 PE/PB/ROE，基本面维度按中性处理")
    elif etf:
        add("muted", f"规模/市值 {fmt_amount((f.get('mktcap') or 0) * 1e8)} · "
                     f"换手 {fmt_pct_plain(f.get('turnover'))} · "
                     f"52周 {pf(f.get('low52'))} ~ {pf(f.get('high52'))}")
        add("muted", "ETF 无个股 PE/PB；重点看流动性、跟踪指数与折溢价")
    else:
        add("muted", f"PE {f.get('pe') if f.get('pe') is not None else '--'}  ·  "
                     f"PB {f.get('pb') if f.get('pb') is not None else '--'}  ·  "
                     f"总市值 {fmt_amount((f.get('mktcap') or 0) * 1e8)}  ·  "
                     f"换手 {fmt_pct_plain(f.get('turnover'))}")
        ind = ev.get("industry") or "/".join(
            x for x in (f.get("sector"), f.get("industry")) if x) or "—"
        add("muted", f"52周 {pf(f.get('low52'))} ~ {pf(f.get('high52'))}  ·  行业 {ind}")
        sec_bits = []
        if f.get("revenue_growth") is not None:
            sec_bits.append(f"营收增长 {f['revenue_growth'] * 100:+.1f}%")
        if f.get("net_margin") is not None:
            sec_bits.append(f"净利率 {f['net_margin'] * 100:.1f}%")
        if f.get("roe") is not None:
            sec_bits.append(f"ROE {f['roe'] * 100:.1f}%")
        if f.get("eps") is not None:
            sec_bits.append(f"EPS {f['eps']:.2f}")
        if sec_bits:
            add("muted", "SEC财务：" + "  ·  ".join(sec_bits))
        if f.get("yield") is not None or f.get("one_year_target") is not None:
            bits = []
            if f.get("yield") is not None:
                bits.append(f"股息率 {f['yield']:.2f}%")
            if f.get("one_year_target") is not None:
                bits.append(f"1年目标 {pf(f['one_year_target'])}")
            if f.get("avg_volume") is not None:
                bits.append(f"平均量 {fmt_vol(f['avg_volume'])}")
            add("muted", "  ·  ".join(bits))

    add("h", "消息面（近24h）")
    ns = ev.get("nstats") or {}
    if ev["mkt"] == "cr":
        add("muted", "加密货币暂无公司公告/资讯评分，消息面按中性处理")
    else:
        add("muted", f"利好 {ns.get('n_pos', 0)} 条 · 利空 {ns.get('n_neg', 0)} 条 · "
                     f"中性 {max(0, len(ev.get('news') or []) - ns.get('n_pos', 0) - ns.get('n_neg', 0))} 条")
        for it in (ev.get("news") or [])[:3]:
            tag = "buy" if it.get("impact") == "利好" else (
                "sell" if it.get("impact") == "利空" else "muted")
            pub = it.get("publisher")
            add(tag, f"· {it.get('time')}  {it.get('title')}"
                     + (f"（{pub}）" if pub else ""))

    add("h", "技术面")
    if not t.get("ma20"):
        add("warn", "日K数据不足，无法计算均线/ATR")
    else:
        add("muted", f"MA5 {pf(t.get('ma5'))}  MA10 {pf(t.get('ma10'))}  "
                     f"MA20 {pf(t.get('ma20'))}  MA60 {pf(t.get('ma60'))}")
        add("muted", f"RSI14 {('%.1f' % t['rsi']) if t.get('rsi') is not None else '--'}  ·  "
                     f"MACD柱 {('%.3f' % t['macd_hist']) if t.get('macd_hist') is not None else '--'}  ·  "
                     f"ATR% {('%.2f%%' % (t['atr'] / t['price'] * 100)) if t.get('atr') and t.get('price') else '--'}")
        add("muted", f"20日波动 {('%.1f%%' % (t['vol20'] * 100)) if t.get('vol20') is not None else '--'}  ·  "
                     f"20日支撑 {pf(t.get('low20'))} / 压力 {pf(t.get('high20'))}  ·  "
                     f"60日区间 {pf(t.get('low60'))} ~ {pf(t.get('high60'))}")
        add("muted", f"趋势 {t.get('trend')}  ·  收盘位置 {t.get('close_pos20', 0) * 100:.0f}%  "
                     f"·  布林 {pf(t.get('boll_low'))} ~ {pf(t.get('boll_up'))}")

    add("h", "风险提示")
    add("warn", "区间基于均线/ATR/支撑压力估算；若放量跌破止损或出现重大利空，应放弃计划。")
    add("warn", "本评价为研究参考，不构成投资建议；个股/ETF/加密均可能大幅波动。")
    return lines


# ---------------------------------------------------------------------------
# 公告消息: 东方财富 A股公告 + 利好/利空关键词标注
# ---------------------------------------------------------------------------

ANNOUNCE_HDR = {"User-Agent": UA["User-Agent"], "Referer": "https://data.eastmoney.com/"}
ANNOUNCE_URL = ("https://np-anotice-stock.eastmoney.com/api/security/ann"
                "?sr=-1&page_size={size}&page_index=1&ann_type=A&client_source=web&stock_list={code}")
ANNOUNCE_DETAIL = "https://data.eastmoney.com/notices/detail/{code}/{art_code}.html"

# 利好/利空关键词(基于公告/资讯标题的启发式判定, 仅供参考; 先判利空再判利好以处理"终止回购"等)
NEWS_NEGATIVE = (
    "减持", "预亏", "亏损", "立案", "处罚", "诉讼", "质押", "减值", "退市",
    "监管", "问询", "警示", "终止", "违约", "解禁", "辞职", "冻结", "调查",
    "谴责", "责令", "更正", "下调", "风险", "不及预期", "闪崩", "暴跌", "停产",
    "downgrade", "cut", "miss", "lawsuit", "probe", "investigation", "recall",
    "layoff", "warning", "plunge", "slump", "decline", "loss", "fraud",
    "bankruptcy", "default", "halt", "delisted", "sell-off", "bearish", "weak",
)
NEWS_POSITIVE = (
    "回购", "增持", "中标", "签约", "预增", "扭亏", "分红", "派息", "股权激励",
    "收购", "重组", "涨价", "获批", "战略合作", "签订", "突破", "超预期", "新高", "强劲",
    "upgrade", "beat", "surge", "rally", "buyback", "dividend", "raises",
    "record", "growth", "profit", "approval", "partnership", "acquisition",
    "bullish", "strong", "jump", "gain", "outperform",
)

_ANNOUNCE_CACHE = {}
_ANNOUNCE_TTL = 300.0   # 公告静态, 缓存 5 分钟

# 自选盯盘表可点击排序的数值列
WATCH_NUMERIC_COLS = ("price", "change", "pct", "pct_prev", "delta", "open", "high", "low",
                      "prev", "volume")


def classify_announcement(title):
    """按公告标题关键词标注影响: 利好 / 利空 / 中性。启发式, 仅作参考。"""
    t = title or ""
    tl = t.lower()
    for kw in NEWS_NEGATIVE:
        if kw.lower() in tl:
            return "利空"
    for kw in NEWS_POSITIVE:
        if kw.lower() in tl:
            return "利好"
    return "中性"


def fetch_announcements(code, size=60):
    """东财 A股公告: 返回 list[dict(date, title, art_code, impact)], 带 TTL 缓存。
    code 为 6 位数字 A股代码(如 600519)。"""
    now = time.time()
    hit = _ANNOUNCE_CACHE.get(code)
    if hit and now - hit[0] < _ANNOUNCE_TTL:
        return hit[1]
    out = []
    try:
        data = json.loads(_http(ANNOUNCE_URL.format(size=size, code=code),
                                ANNOUNCE_HDR, timeout=8).decode("utf-8", "replace"))
        for it in (data.get("data") or {}).get("list") or []:
            title = it.get("title") or ""
            out.append({
                "date": (it.get("notice_date") or "")[:10],
                "title": title,
                "art_code": it.get("art_code") or "",
                "impact": classify_announcement(title),
            })
    except Exception:
        pass
    _ANNOUNCE_CACHE[code] = (now, out)
    return out


# ---------------------------------------------------------------------------
# 24小时消息面: 东方财富个股资讯(三市场) + 利好/利空标注
# ---------------------------------------------------------------------------

NEWS_LIST_HDR = {"User-Agent": UA["User-Agent"], "Referer": "https://quote.eastmoney.com/"}
NEWS_LIST_URL = ("https://np-listapi.eastmoney.com/comm/web/getListInfo"
                 "?client=web&mTypeAndCode={code}&type=1&pageSize={size}&pageIndex=1")
NEWS_WINDOW_H = 24.0        # 消息面时间窗(小时)

_STOCK_NEWS_CACHE = {}      # em_code -> (ts, items24h, stats)
_STOCK_NEWS_TTL = 600.0     # 资讯列表缓存 10 分钟


def em_news_code(mkt, disp, qt_code=""):
    """东财个股资讯的市场代码: 1=沪 0=深/北 116=港 105/106/107=美股(按交易所)。
    美股交易所从行情完整代码后缀判断(.OQ纳斯达克/.N纽交所/.A美交所)。"""
    if mkt == "sh":
        return "1." + disp
    if mkt == "hk":
        return "116." + disp
    if mkt == "us":
        suf = (qt_code or "").upper()
        if suf.endswith(".N"):
            return "106." + disp
        if suf.endswith(".A"):
            return "107." + disp
        return "105." + disp
    return "0." + disp                     # sz / bj


def _parse_dt(s):
    """'2026-08-27 14:07:28' -> 本地时间戳; 解析失败返回 None。"""
    try:
        return time.mktime(time.strptime(s, "%Y-%m-%d %H:%M:%S"))
    except (TypeError, ValueError):
        return None


def fetch_stock_news(mkt, disp, qt_code="", size=40):
    """东财个股资讯: 取最近 size 条, 过滤出近 24h 内条目并标注利好/利空。
    返回 (items24h, stats): items=[{time,title,url,impact}], stats={n_pos,n_neg}。带 10 分钟 TTL 缓存。"""
    key = em_news_code(mkt, disp, qt_code)
    now = time.time()
    hit = _STOCK_NEWS_CACHE.get(key)
    if hit and now - hit[0] < _STOCK_NEWS_TTL:
        return hit[1], hit[2]
    items = []
    stats = {"n_pos": 0, "n_neg": 0}
    try:
        data = json.loads(_http(NEWS_LIST_URL.format(code=key, size=size),
                                NEWS_LIST_HDR, timeout=8).decode("utf-8", "replace"))
        for it in (data.get("data") or {}).get("list") or []:
            t = str(it.get("Art_ShowTime") or "")[:19]
            ts = _parse_dt(t)
            if ts is None or not (0 <= now - ts <= NEWS_WINDOW_H * 3600):
                continue
            impact = classify_announcement(it.get("Art_Title") or "")
            if impact == "利好":
                stats["n_pos"] += 1
            elif impact == "利空":
                stats["n_neg"] += 1
            items.append({"time": t[5:16], "title": it.get("Art_Title") or "",
                          "url": it.get("Art_Url") or "", "impact": impact})
    except Exception:
        pass
    _STOCK_NEWS_CACHE[key] = (now, items, stats)
    return items, stats


# ---------------------------------------------------------------------------
# 7x24 全球快讯: 新浪财经直播
# ---------------------------------------------------------------------------

ZB_URL = ("https://zhibo.sina.com.cn/api/zhibo/feed?page=1&page_size={n}"
          "&zhibo_id=152&tag_id=0&dire=f&dpc=1")
ZB_HDR = {"User-Agent": UA["User-Agent"], "Referer": "https://finance.sina.com.cn/7x24/"}


def fetch_flash_news(n=50):
    """新浪 7x24 财经快讯(最新 n 条, 新->旧): list[dict(time,text,impact,url)]。失败返回 []。"""
    try:
        raw = _http(ZB_URL.format(n=n), ZB_HDR, timeout=8).decode("utf-8", "replace")
        feed = ((json.loads(raw).get("result") or {}).get("data") or {}).get("feed") or {}
        out = []
        for it in feed.get("list") or []:
            text = (it.get("rich_text") or "").strip()
            if not text:
                continue
            out.append({"time": str(it.get("create_time") or "")[5:16],
                        "text": text, "url": it.get("docurl") or "",
                        "impact": classify_announcement(text)})
        return out
    except Exception:
        return []


def fmt_news(r):
    """选股器「24h消息」列: 利好N·利空M / 无 / --。"""
    p, n = r.get("news_pos"), r.get("news_neg")
    if p is None and n is None:
        return "--"
    if not p and not n:
        return "无"
    if p and n:
        return f"利好{p}·利空{n}"
    return f"利好{p}" if p else f"利空{n}"


# ---------------------------------------------------------------------------
# 问财选股(可选依赖): 同花顺 iwencai 自然语言筛选
# ---------------------------------------------------------------------------
# 依赖: pip install pywencai  +  Node.js(hexin-v token 生成)  +  登录cookie
# iwencai 接口有同花顺风控(匿名 403 Access Denied), 需要浏览器 cookie:
#   打开 www.iwencai.com -> F12 -> 控制台执行 document.cookie -> 复制粘贴到问财页输入框
# 本体保持零依赖: 未安装 pywencai/Node 时问财页仅提示, 其余功能不受影响。
# ---------------------------------------------------------------------------

_PYWENCAI_MOD = None
_PYWENCAI_PATCHED = False


def _patch_pywencai_headers():
    """补齐 Origin/Referer 并固定浏览器 UA。
    iwencai 网关校验这些头, 缺失会被 WAF 直接 403(2026 年起, pywencai 官方未适配);
    cookie 须含完整登录态(sess_tk/ticket/utk 等), 只带部分字段会报「未登陆」。"""
    global _PYWENCAI_PATCHED
    if _PYWENCAI_PATCHED:
        return
    # pywencai 通过 Node 生成 token; 屏蔽 Node 的 punycode 弃用警告
    os.environ.setdefault("NODE_OPTIONS", "--no-deprecation")
    import pywencai.wencai as _wc_mod
    _orig = _wc_mod.headers

    def patched(cookie=None, user_agent=None):
        h = _orig(cookie, user_agent)
        h["User-Agent"] = ("Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 "
                           "(KHTML, like Gecko) Chrome/126.0.0.0 Safari/537.36")
        h["Origin"] = "https://www.iwencai.com"
        h["Referer"] = "https://www.iwencai.com/"
        h["Accept"] = "application/json"
        return h

    _wc_mod.headers = patched
    _PYWENCAI_PATCHED = True


def _wencai_ready():
    """(可用, 原因)。pywencai 与 Node.js 均在时可用。"""
    if importlib.util.find_spec("pywencai") is None:
        return False, "未安装 pywencai (pip install pywencai)"
    if shutil.which("node") is None:
        return False, "未安装 Node.js (生成 hexin-v token 需要)"
    return True, ""


def _wc_cell(v):
    """DataFrame 单元格 -> 可展示/可排序的纯量; NaN/None -> ""。"""
    if v is None:
        return ""
    if isinstance(v, float):
        if v != v:                      # NaN
            return ""
        return round(v, 4)
    if isinstance(v, int):
        return v
    if hasattr(v, "isoformat"):         # date / datetime
        return v.isoformat()[:10]
    return str(v)


def _wc_num(v):
    """尝试把单元格识别为数值; 失败返回 None。数字型字符串(如 '29.9692...')也识别,
    但不含小数点的纯数字串(可能是代码/日期)不转, 避免 '000625' 被破坏。"""
    if isinstance(v, (int, float)):
        return float(v)
    if isinstance(v, str) and "." in v:
        try:
            return float(v)
        except ValueError:
            pass
    return None


def _wc_disp(v):
    """单元格展示文本: 大数加千分位, 小数去尾零; 数字型字符串先转数值再格式化。"""
    if isinstance(v, str):
        f = _wc_num(v)
        if f is not None:
            v = f
    if isinstance(v, float):
        if abs(v) >= 1e5:
            return f"{v:,.0f}"
        s = f"{v:.3f}".rstrip("0").rstrip(".")
        return s if s not in ("", "-") else "0"
    return str(v)


def wencai_query(query, cookie=""):
    """执行问财自然语言查询, 返回 (cols, rows)。cols=list[str], rows=list[list]。
    失败抛 RuntimeError(中文原因)。应在后台线程调用(阻塞网络, 首次加载 pandas 较慢)。"""
    global _PYWENCAI_MOD
    ok, why = _wencai_ready()
    if not ok:
        raise RuntimeError(why)
    if _PYWENCAI_MOD is None:
        import pywencai
        _PYWENCAI_MOD = pywencai
    _patch_pywencai_headers()
    kw = {"query": query, "log": False}
    if cookie.strip():
        kw["cookie"] = cookie.strip()
    try:
        df = _PYWENCAI_MOD.get(**kw)
    except Exception as e:
        # pywencai 内部重试 10 次失败后返回 None -> AttributeError; 被 403/401 拦截时即此表现
        raise RuntimeError(f"问财查询失败({type(e).__name__}): cookie 缺失/失效会报 403/未登陆, "
                           f"请从浏览器重新复制完整 document.cookie 后再试")
    if df is None or not hasattr(df, "columns") or len(df) == 0:
        raise RuntimeError("问财无匹配结果(换个条件描述试试, 如「今日涨幅大于4%」)")
    cols = [" / ".join(map(str, c)) if isinstance(c, tuple) else str(c) for c in df.columns]
    rows = [[_wc_cell(v) for v in row] for row in df.values.tolist()]
    # 代码/名称列提到最前, 便于阅读与右键操作
    front = [c for c in ("股票代码", "股票简称") if c in cols]
    if front:
        idx = [cols.index(c) for c in front]
        rest = [i for i in range(len(cols)) if i not in idx]
        order = idx + rest
        cols = [cols[i] for i in order]
        rows = [[r[i] for i in order] for r in rows]
    return cols, rows


def _wc_code_of(value):
    """问财代码列取 6 位 A股代码: '600519.SH' / '600519' -> '600519'。"""
    s = str(value or "")
    digits = "".join(ch for ch in s if ch.isdigit())
    return digits[:6] if len(digits) >= 6 else s


# ---------------------------------------------------------------------------
# 主窗口
# ---------------------------------------------------------------------------

def export_rows_csv(parent, title, default_name, headers, rows):
    """弹出保存对话框并写 UTF-8-BOM CSV(Excel 直接打开不乱码)。"""
    path = filedialog.asksaveasfilename(
        parent=parent, title=title, defaultextension=".csv",
        initialfile=default_name,
        filetypes=[("CSV 文件", "*.csv"), ("所有文件", "*.*")])
    if not path:
        return ""
    try:
        with open(path, "w", encoding="utf-8-sig", newline="") as f:
            w = csv.writer(f)
            w.writerow(headers)
            w.writerows(rows)
    except Exception as e:
        messagebox.showerror("导出失败", str(e), parent=parent)
        return ""
    return path


class FlowFrame(ttk.Frame):
    """按可用宽度自动换行的控件容器。"""

    def __init__(self, master=None, padding=0, **kw):
        super().__init__(master, padding=padding, **kw)
        self._items = []
        self._last_width = 0
        self._pending = None
        self.bind("<Configure>", self._on_configure)

    def add(self, widget, padx=2):
        self._items.append((widget, padx))
        self._schedule()
        return widget

    def _schedule(self):
        if self._pending:
            try:
                self.after_cancel(self._pending)
            except Exception:
                pass
        self._pending = self.after(30, self._reflow)

    def _on_configure(self, event):
        if abs(event.width - self._last_width) >= 8:
            self._schedule()

    def _reflow(self):
        self._pending = None
        width = self.winfo_width()
        if width <= 1:
            return
        self._last_width = width
        row = col = 0
        x = 0
        def span(pad):
            if isinstance(pad, (tuple, list)):
                return sum(v for v in pad if isinstance(v, (int, float)))
            return pad * 2

        for w, pad in self._items:
            if not w.winfo_exists():
                continue
            rw = max(w.winfo_reqwidth(), w.winfo_width())
            if col and x + rw + span(pad) > width:
                row += 1
                col = 0
                x = 0
            w.grid(row=row, column=col, sticky="w", padx=pad, pady=1)
            x += rw + span(pad)
            col += 1


class StockMonitorApp:
    def __init__(self, root):
        self.root = root
        root.title("A股·ETF·港股·美股·加密 行情监控 + 选股/评估 (延时行情)")
        root.geometry("1420x760")

        self._stop = False
        self._queue = queue.Queue()
        self._refresh_event = threading.Event()
        self._lock = threading.Lock()
        self._screen_busy = False
        self._screen_queue = queue.Queue()

        self.watchlist = []
        self.index_results = {}
        self.stock_results = {}      # symbol -> (data, market)
        self.last_update = ""
        self.quote_source = ""
        self.cn_color = True

        # 选股器状态
        self.screen_rows = []        # 过滤+排序后的完整结果
        self.screen_page = 0
        self.screen_page_size = 50

        # 自选盯盘排序状态
        self.watch_sort_col = None
        self.watch_sort_desc = False

        # 选股器排序状态(表头点击)
        self.screen_sort_col = None
        self.screen_sort_desc = False

        # 因子选股状态
        self._factor_busy = False
        self._factor_cancel = threading.Event()
        self._factor_queue = queue.Queue()
        self._eval_busy = False
        self._eval_queue = queue.Queue()
        self._eval_last_code = ""
        self._eval_last_report = ""
        self._eval_last_lines = []
        self.factor_rows = []
        self.factor_stats = []
        self.factor_meta = {}
        self.factor_wf = {}
        self.factor_vol_stats = {}
        self.factor_sort_col = None
        self.factor_sort_desc = True
        self.factor_stat_sort_col = None
        self.factor_stat_sort_desc = True

        self._load_config()
        self._build_ui()
        self._start_worker()
        self.root.after(250, self._screen_pump)
        self.root.after(300, self._factor_pump)
        self.root.after(350, self._eval_pump)
        root.protocol("WM_DELETE_WINDOW", self._on_close)
        root.report_callback_exception = self._on_ui_error

    def _on_ui_error(self, exc, val, tb):
        _LOG.error("界面回调异常", exc_info=(exc, val, tb))
        try:
            messagebox.showerror("运行错误", f"{exc.__name__}: {val}",
                                 parent=self.root)
        except Exception:
            pass

    # ---------------- 配置 ----------------
    def _load_config(self):
        try:
            with open(CONFIG_FILE, "r", encoding="utf-8") as f:
                cfg = json.load(f)
            self.watchlist = [str(t).upper() for t in cfg.get("watchlist", DEFAULT_WATCHLIST)]
            self.interval = int(cfg.get("interval", 5))
            self.cn_color = bool(cfg.get("cn_color", True))
            self.screen_market = str(cfg.get("screen_market", "a"))
            if self.screen_market not in ("a", "us", "etf"):
                self.screen_market = "a"
            self.wencai_cookie = str(cfg.get("wencai_cookie", ""))
            self.wencai_last_query = str(cfg.get("wencai_last_query", ""))

            def _ci(key, default, lo, hi):
                try:
                    return max(lo, min(hi, int(cfg.get(key, default))))
                except (TypeError, ValueError):
                    return default

            def _cf(key, default, lo, hi):
                try:
                    return max(lo, min(hi, float(cfg.get(key, default))))
                except (TypeError, ValueError):
                    return default

            self.factor_limit = _ci("factor_limit", 300, 50, 800)
            self.factor_lookback = _ci("factor_lookback", 250, 80, 300)
            self.factor_horizon = 5 if cfg.get("factor_horizon") == 5 else 1
            self.factor_threshold = _cf("factor_threshold", 60.0, 0.0, 100.0)
            self.factor_exclude_st = bool(cfg.get("factor_exclude_st", True))
            self.factor_exclude_limit = bool(cfg.get("factor_exclude_limit", True))
            _ma = str(cfg.get("factor_ma", "全部"))
            _ma = {"上20": "站上MA20", "下20": "跌破MA20"}.get(_ma, _ma)
            _valid = ("全部", "站上MA5", "跌破MA5", "站上MA10", "跌破MA10",
                      "站上MA20", "跌破MA20", "站上MA60", "跌破MA60")
            self.factor_ma = _ma if _ma in _valid else "全部"
            _vol = str(cfg.get("factor_vol", "全部"))
            _vvalid = ("全部", "≈1倍(0.8~1.2)", "0.5~1.5倍",
                       "放量≥1.5倍", "放量≥2倍", "放量≥3倍", "缩量≤0.8倍")
            self.factor_vol = _vol if _vol in _vvalid else "全部"
            _fm = str(cfg.get("factor_market", "all"))
            self.factor_market = _fm if _fm in ("a", "etf", "crypto", "us", "all") else "all"
            self.factor_show_n = _ci("factor_show_n", 50, 20, 100)
        except Exception:
            self.watchlist = list(DEFAULT_WATCHLIST)
            self.interval = 5
            self.cn_color = True
            self.screen_market = "a"
            self.wencai_cookie = ""
            self.wencai_last_query = ""
            self.factor_limit = 300
            self.factor_lookback = 250
            self.factor_horizon = 1
            self.factor_threshold = 60.0
            self.factor_exclude_st = True
            self.factor_exclude_limit = True
            self.factor_ma = "全部"
            self.factor_vol = "全部"
            self.factor_market = "all"
            self.factor_show_n = 50
        self.interval = max(3, min(3600, self.interval))

    def _save_config(self):
        try:
            with open(CONFIG_FILE, "w", encoding="utf-8") as f:
                json.dump({"watchlist": self.watchlist, "interval": self.interval,
                           "cn_color": self.cn_color,
                           "screen_market": getattr(self, "screen_market", "a"),
                           "wencai_cookie": getattr(self, "wencai_cookie", ""),
                           "wencai_last_query": getattr(self, "wencai_last_query", ""),
                           "factor_limit": getattr(self, "factor_limit", 300),
                           "factor_lookback": getattr(self, "factor_lookback", 250),
                           "factor_horizon": getattr(self, "factor_horizon", 1),
                           "factor_threshold": getattr(self, "factor_threshold", 60.0),
                           "factor_exclude_st": getattr(self, "factor_exclude_st", True),
                           "factor_exclude_limit": getattr(self, "factor_exclude_limit", True),
                           "factor_ma": getattr(self, "factor_ma", "全部"),
                           "factor_vol": getattr(self, "factor_vol", "全部"),
                           "factor_market": getattr(self, "factor_market", "a"),
                           "factor_show_n": getattr(self, "factor_show_n", 50)},
                          f, ensure_ascii=False, indent=2)
        except Exception as e:
            print("配置保存失败:", e)

    def _up_color(self):
        if self.cn_color:
            return COLOR_UP_DEFAULT, COLOR_DOWN_DEFAULT
        return COLOR_DOWN_DEFAULT, COLOR_UP_DEFAULT

    # ---------------- UI 骨架 ----------------
    def _apply_theme(self, style):
        """币安风格深色主题: #0B0E11 底 + #F0B90B 强调色。"""
        style.theme_use("clam")
        self.root.configure(bg=BG_ROOT)
        self.root.option_add("*TCombobox*Listbox.background", BG_CARD)
        self.root.option_add("*TCombobox*Listbox.foreground", FG_TEXT)
        self.root.option_add("*TCombobox*Listbox.selectBackground", ACCENT)
        self.root.option_add("*TCombobox*Listbox.selectForeground", BG_ROOT)
        style.configure(".", background=BG_ROOT, foreground=FG_TEXT,
                        fieldbackground=BG_CARD, bordercolor=BORDER,
                        lightcolor=BG_PANEL, darkcolor=BG_PANEL,
                        troughcolor=BG_PANEL, focuscolor=ACCENT,
                        font=("Microsoft YaHei", 9))
        style.configure("TFrame", background=BG_ROOT)
        style.configure("Card.TFrame", background=BG_PANEL)
        style.configure("TLabel", background=BG_ROOT, foreground=FG_TEXT)
        style.configure("Muted.TLabel", background=BG_ROOT, foreground=FG_MUTED)
        style.configure("TButton", background=BG_CARD, foreground=FG_TEXT,
                        bordercolor=BORDER, focuscolor=BG_CARD,
                        padding=(10, 4), relief="flat")
        style.map("TButton",
                  background=[("active", BG_HOVER), ("disabled", BG_PANEL)],
                  foreground=[("disabled", FG_MUTED)])
        style.configure("Accent.TButton", background=ACCENT, foreground="#0B0E11",
                        bordercolor=ACCENT, focuscolor=ACCENT,
                        font=("Microsoft YaHei", 9, "bold"))
        style.map("Accent.TButton",
                  background=[("active", ACCENT_HOVER), ("disabled", "#5E4E0C")],
                  foreground=[("disabled", "#B8A15A")])
        style.configure("TEntry", fieldbackground=BG_CARD, foreground=FG_TEXT,
                        insertcolor=FG_TEXT, bordercolor=BORDER,
                        lightcolor=BG_CARD, darkcolor=BG_CARD, padding=3)
        style.map("TEntry", bordercolor=[("focus", ACCENT)])
        style.configure("TCombobox", fieldbackground=BG_CARD, background=BG_CARD,
                        foreground=FG_TEXT, arrowcolor=FG_MUTED,
                        bordercolor=BORDER, padding=3)
        style.map("TCombobox",
                  fieldbackground=[("readonly", BG_CARD)],
                  foreground=[("readonly", FG_TEXT)],
                  selectbackground=[("readonly", BG_CARD)],
                  selectforeground=[("readonly", FG_TEXT)],
                  arrowcolor=[("active", ACCENT)])
        style.configure("TSpinbox", fieldbackground=BG_CARD, foreground=FG_TEXT,
                        arrowcolor=FG_MUTED, bordercolor=BORDER)
        style.configure("TCheckbutton", background=BG_ROOT, foreground=FG_TEXT,
                        indicatorcolor=BG_CARD, focuscolor=BG_ROOT)
        style.map("TCheckbutton",
                  background=[("active", BG_ROOT)],
                  foreground=[("active", FG_TEXT)],
                  indicatorcolor=[("selected", ACCENT)])
        style.configure("TNotebook", background=BG_ROOT, bordercolor=BORDER,
                        tabmargins=(8, 6, 8, 0))
        style.configure("TNotebook.Tab", background=BG_PANEL, foreground=FG_MUTED,
                        padding=(18, 8), bordercolor=BORDER)
        style.map("TNotebook.Tab",
                  background=[("selected", BG_CARD), ("active", BG_HOVER)],
                  foreground=[("selected", ACCENT), ("active", FG_TEXT)])
        style.configure("Treeview", background=BG_PANEL, fieldbackground=BG_PANEL,
                        foreground=FG_TEXT, bordercolor=BORDER, rowheight=25,
                        font=("Microsoft YaHei", 9))
        style.map("Treeview",
                  background=[("selected", BG_HOVER)],
                  foreground=[("selected", FG_TEXT)])
        style.configure("Treeview.Heading", background=BG_CARD, foreground=FG_MUTED,
                        bordercolor=BORDER, relief="flat",
                        font=("Microsoft YaHei", 9, "bold"), padding=(4, 6))
        style.map("Treeview.Heading",
                  background=[("active", BG_HOVER)],
                  foreground=[("active", FG_TEXT)])
        style.configure("Vertical.TScrollbar", background=BG_CARD, troughcolor=BG_ROOT,
                        arrowcolor=FG_MUTED, bordercolor=BG_ROOT)
        style.configure("Horizontal.TScrollbar", background=BG_CARD, troughcolor=BG_ROOT,
                        arrowcolor=FG_MUTED, bordercolor=BG_ROOT)
        style.configure("TLabelframe", background=BG_ROOT, foreground=FG_MUTED,
                        bordercolor=BORDER)
        style.configure("TLabelframe.Label", background=BG_ROOT, foreground=FG_MUTED)
        style.configure("TPanedwindow", background=BG_ROOT)
        style.configure("TPanedwindow.Sash", background=BORDER)

    def _build_ui(self):
        style = ttk.Style()
        self._apply_theme(style)
        hdr = ttk.Frame(self.root, padding=(16, 8, 16, 2))
        hdr.pack(fill="x")
        ttk.Label(hdr, text="FINA", font=("Segoe UI", 15, "bold"),
                  foreground=ACCENT).pack(side="left")
        ttk.Label(hdr, text="  行情监控 · 选股 · 因子研究",
                  foreground=FG_MUTED).pack(side="left")
        ttk.Label(hdr, text="延时行情 · 仅供研究，不构成投资建议",
                  foreground=FG_MUTED).pack(side="right")
        nb = ttk.Notebook(self.root)
        nb.pack(fill="both", expand=True)
        self.nb = nb
        self.tab_watch = ttk.Frame(nb)
        self.tab_screen = ttk.Frame(nb)
        self.tab_factor = ttk.Frame(nb)
        self.tab_eval = ttk.Frame(nb)
        self.tab_feed = ttk.Frame(nb)
        self.tab_wencai = ttk.Frame(nb)
        nb.add(self.tab_watch, text="  自选盯盘  ")
        nb.add(self.tab_screen, text="  选股器(A股)  ")
        nb.add(self.tab_factor, text="  因子选股  ")
        nb.add(self.tab_eval, text="  综合评估  ")
        nb.add(self.tab_feed, text="  7x24快讯  ")
        nb.add(self.tab_wencai, text="  问财选股  ")
        self._build_watch_tab()
        self._build_screen_tab()
        self._build_factor_tab()
        self._build_eval_tab()
        self._build_feed_tab()
        self._build_wencai_tab()

    # ================ 自选盯盘 ================
    def _build_watch_tab(self):
        # 顶部指数条
        idx_frame = ttk.Frame(self.tab_watch, padding=(8, 6))
        idx_frame.pack(fill="x")
        self.index_vars = {}
        self.index_labels = {}
        for name, tcode in INDEXES:
            box = ttk.Frame(idx_frame)
            box.pack(side="left", padx=10)
            ttk.Label(box, text=name, font=("Microsoft YaHei", 9)).pack(anchor="w")
            v = tk.StringVar(value="--")
            self.index_vars[name] = v
            lbl = ttk.Label(box, textvariable=v, font=("Consolas", 14, "bold"))
            lbl.pack(anchor="w")
            self.index_labels[name] = lbl

        # 控制栏
        ctrl = ttk.Frame(self.tab_watch, padding=(8, 4))
        ctrl.pack(fill="x")
        ttk.Label(ctrl, text="自选股(美股/A股/港股):").pack(side="left")
        self.add_var = tk.StringVar()
        entry = ttk.Entry(ctrl, textvariable=self.add_var, width=30)
        entry.pack(side="left", padx=4)
        entry.bind("<Return>", lambda e: self._add_symbols())
        ttk.Button(ctrl, text="添加", command=self._add_symbols,
                   style="Accent.TButton").pack(side="left", padx=2)
        ttk.Button(ctrl, text="删除选中", command=self._remove_selected).pack(side="left", padx=2)
        ttk.Button(ctrl, text="立即刷新", command=self._refresh_now).pack(side="left", padx=2)
        ttk.Label(ctrl, text="  刷新间隔(秒):").pack(side="left")
        self.interval_var = tk.StringVar(value=str(self.interval))
        ttk.Spinbox(ctrl, from_=3, to=3600, textvariable=self.interval_var,
                    width=6, command=self._apply_interval).pack(side="left")
        self.color_var = tk.BooleanVar(value=self.cn_color)
        ttk.Checkbutton(ctrl, text="红涨绿跌", variable=self.color_var,
                        command=self._toggle_color).pack(side="left", padx=10)

        # 表格
        cols = ("mkt", "code", "name", "price", "change", "pct", "pct_prev", "delta",
                "open", "high", "low", "prev", "volume", "time")
        headers = ("市场", "代码", "名称", "现价", "涨跌", "涨跌幅", "昨涨幅", "涨幅差",
                   "开盘", "最高", "最低", "昨收", "成交量", "更新时间")
        widths = (48, 76, 112, 82, 82, 82, 76, 76, 78, 78, 78, 78, 90, 140)
        self.watch_cols = cols
        self.watch_headers = dict(zip(cols, headers))
        tf = ttk.Frame(self.tab_watch, padding=(8, 4))
        tf.pack(fill="both", expand=True)
        self.tree = ttk.Treeview(tf, columns=cols, show="headings")
        for c, h, w in zip(cols, headers, widths):
            self.tree.heading(c, text=h, command=lambda col=c: self._sort_watch(col))
            self.tree.column(c, width=w, anchor="e")
        for c in ("name", "code", "mkt"):
            self.tree.column(c, anchor="w")
        self.tree.column("time", anchor="center")
        vsb = ttk.Scrollbar(tf, orient="vertical", command=self.tree.yview)
        self.tree.configure(yscrollcommand=vsb.set)
        self.tree.pack(side="left", fill="both", expand=True)
        vsb.pack(side="right", fill="y")
        self.tree.tag_configure("up", foreground=COLOR_UP_DEFAULT)
        self.tree.tag_configure("down", foreground=COLOR_DOWN_DEFAULT)
        self.tree.tag_configure("flat", foreground=COLOR_FLAT)
        self.tree.bind("<Double-1>", self._open_detail)
        self.tree.bind("<Button-3>", self._on_watch_right_click)

        self.status_var = tk.StringVar(value="加载中...")
        ttk.Label(self.tab_watch, textvariable=self.status_var, anchor="w",
                  padding=(8, 4)).pack(fill="x")

    def _start_worker(self):
        threading.Thread(target=self._worker, daemon=True).start()

    def _worker(self):
        while not self._stop:
            try:
                res = self._fetch_all()
                res["ts"] = time.strftime("%H:%M:%S")
                self._queue.put(res)
            except Exception as e:
                print("抓取异常:", e)
                _LOG.exception("自选行情抓取异常")
            self._refresh_event.wait(timeout=self.interval)
            self._refresh_event.clear()

    def _fetch_all(self):
        with self._lock:
            syms = list(self.watchlist)

        items = []
        crypto_syms = []
        for sym in syms:
            c = classify_symbol(sym)
            if not c:
                continue
            if c[2] == "cr":
                crypto_syms.append(sym)
            else:
                items.append((sym, sina_code(sym), c[0]))
        for _name, tcode in INDEXES:
            items.append((tcode, sina_code(tcode), tcode))

        quotes, sources = fetch_quotes_auto(items)
        crypto_quotes, _crypto_src = ({}, "")
        if crypto_syms:
            crypto_quotes, _crypto_src = fetch_crypto_quotes(crypto_syms)
            quotes.update(crypto_quotes)

        stocks = {}
        prev_items = []
        for sym in syms:
            c = classify_symbol(sym)
            if not c:
                continue
            data = quotes.get(sym)
            if not data:
                continue
            _tcode, _disp, mkt = c
            ksym = ("us" + data["qt_code"]) if (mkt == "us" and data.get("qt_code")) else c[0]
            stocks[sym] = [data, mkt]
            prev_items.append((sym, ksym))

        def attach_prev(item):
            sym, ksym = item
            m = fetch_prev_metrics(ksym)
            return sym, m

        if prev_items:
            with ThreadPoolExecutor(max_workers=20) as ex:
                for sym, m in ex.map(attach_prev, prev_items):
                    data = stocks.get(sym)
                    if data and m and m.get("p") is not None and data[0].get("pct") is not None:
                        data[0]["pct_prev"] = m["p"]
                        data[0]["delta"] = round(data[0]["pct"] - m["p"], 2)
        stocks = {k: tuple(v) for k, v in stocks.items()}

        indexes = {}
        for name, tcode in INDEXES:
            data = quotes.get(tcode)
            if data:
                indexes[name] = data
        return {"stocks": stocks, "indexes": indexes,
                "source": f"新浪批量 {sources['sina']} · 腾讯回退 {sources['tencent']}"
                          f" · Yahoo {sources.get('yahoo', 0)}"
                          f" · 东财 {sources.get('eastmoney', 0)}"
                          f" · 加密 {len(crypto_quotes)}"}

    def _poll(self):
        try:
            while True:
                res = self._queue.get_nowait()
                self.stock_results = res.get("stocks", {})
                self.index_results = res.get("indexes", {})
                self.last_update = res.get("ts", "")
                self.quote_source = res.get("source", self.quote_source)
                self._render_indexes()
                self._render_table()
        except queue.Empty:
            pass
        self.root.after(300, self._poll)

    def _render_indexes(self):
        up, down = self._up_color()
        for name, _tcode in INDEXES:
            d = self.index_results.get(name)
            v = self.index_vars[name]
            lbl = self.index_labels[name]
            if not d or d.get("price") is None:
                v.set("--")
                lbl.configure(foreground=COLOR_FLAT)
                continue
            chg = d.get("change") or 0
            color = COLOR_FLAT if chg == 0 else (up if chg > 0 else down)
            v.set(f"{fmt_price(d['price'])} {fmt_signed(d.get('change'))} {fmt_pct(d.get('pct'))}")
            lbl.configure(foreground=color)

    def _render_table(self):
        up, down = self._up_color()
        self.tree.delete(*self.tree.get_children())
        with self._lock:
            syms = list(self.watchlist)
        if self.watch_sort_col:
            syms = self._sorted_watch(syms)
        for sym in syms:
            entry = self.stock_results.get(sym)
            c = classify_symbol(sym)
            mkt = c[2] if c else ""
            if not entry or entry[0] is None:
                self.tree.insert("", "end", values=(
                    MARKET_LABEL.get(mkt, "?"), sym, "--", "--", "--", "--", "--",
                    "--", "--", "--", "--", "获取失败"), tags=("flat",))
                continue
            d, _ = entry
            chg = d.get("change") or 0
            tag = "flat" if chg == 0 else ("up" if chg > 0 else "down")
            etf = is_etf(sym)
            if mkt == "cr":
                pf, sf = fmt_crypto_price, fmt_crypto_signed
            elif etf:
                pf = lambda v: "--" if v is None else f"{v:.3f}"
                sf = lambda v: "--" if v is None else f"{v:+.3f}"
            else:
                pf, sf = fmt_price, fmt_signed
            vals = (
                "ETF/LOF" if etf else MARKET_LABEL.get(mkt, "?"),
                sym,
                d.get("name") or "",
                pf(d.get("price")),
                sf(d.get("change")),
                fmt_pct(d.get("pct")),
                fmt_pct(d.get("pct_prev")),
                fmt_pct(d.get("delta")),
                pf(d.get("open")),
                pf(d.get("high")),
                pf(d.get("low")),
                pf(d.get("prev_close")),
                fmt_vol(d.get("volume")),
                d.get("time") or "",
            )
            self.tree.insert("", "end", values=vals, tags=(tag,))
        n = len(syms)
        ok = len(self.stock_results)
        src = self.quote_source or "新浪/腾讯自动"
        self.status_var.set(
            f"数据源: {src} (延时) · 最后刷新 {self.last_update} · 共 {n} 只 · 正常 {ok} · "
            f"双击行打开详情页"
        )

    # ---------------- 自选股交互 ----------------
    def _add_symbols(self):
        raw = self.add_var.get()
        if not raw.strip():
            return
        added = []
        for part in raw.replace(",", " ").replace(";", " ").replace("，", " ").split():
            c = classify_symbol(part)
            if not c:
                continue
            _tcode, disp, _mkt = c
            with self._lock:
                if disp not in self.watchlist:
                    self.watchlist.append(disp)
                    added.append(disp)
        self.add_var.set("")
        if added:
            self._save_config()
            self._refresh_event.set()
        else:
            messagebox.showinfo("提示", "未添加新代码(可能已存在或格式不对)。\n"
                                "示例: AAPL / 600519 / 00700 / sh600519")

    def _remove_selected(self):
        sel = self.tree.selection()
        if not sel:
            return
        for item in sel:
            code = self.tree.item(item, "values")[1]
            with self._lock:
                if code in self.watchlist:
                    self.watchlist.remove(code)
        self._save_config()
        self._refresh_event.set()

    def _refresh_now(self):
        self._refresh_event.set()

    def _apply_interval(self):
        try:
            self.interval = max(3, min(3600, int(self.interval_var.get())))
        except ValueError:
            self.interval = 5
        self.interval_var.set(str(self.interval))
        self._save_config()
        self._refresh_event.set()

    def _toggle_color(self):
        self.cn_color = self.color_var.get()
        self._save_config()
        self._render_indexes()
        self._render_table()

    def _open_detail(self, _event):
        sel = self.tree.selection()
        if not sel:
            return
        code = self.tree.item(sel[0], "values")[1]
        c = classify_symbol(code)
        if not c:
            return
        _tcode, disp, mkt = c
        webbrowser.open(detail_url(mkt, disp))

    # ================ 选股器 ================
    def _build_screen_tab(self):
        top = FlowFrame(self.tab_screen, padding=(8, 6))
        top.pack(fill="x")
        add = top.add

        _mkt_label = {"a": "A股全市场选股", "us": "美股全市场选股",
                      "etf": "ETF选股"}.get(getattr(self, "screen_market", "a"), "A股全市场选股")
        self.screen_title_var = tk.StringVar(value=_mkt_label)
        add(ttk.Label(top, textvariable=self.screen_title_var,
                      font=("Microsoft YaHei", 11, "bold")), padx=(0, 8))
        add(ttk.Label(top, text="市场"))
        self.screen_market_var = tk.StringVar(
            value={"a": "A股", "us": "美股", "etf": "ETF"}.get(
                getattr(self, "screen_market", "a"), "A股"))
        add(ttk.Combobox(top, textvariable=self.screen_market_var, width=6,
                         state="readonly", values=("A股", "美股", "ETF")))
        self.screen_market_var.trace_add("write", lambda *a: self._screen_market_changed())

        add(ttk.Label(top, text="涨幅"))
        self.f_min_var = tk.StringVar(value="4.0")
        add(ttk.Entry(top, textvariable=self.f_min_var, width=5))
        add(ttk.Label(top, text="% ~"))
        self.f_max_var = tk.StringVar(value="5.0")
        add(ttk.Entry(top, textvariable=self.f_max_var, width=5))
        add(ttk.Label(top, text="%"))

        self.f_x1_label = add(ttk.Label(top, text="量比≥"))
        self.f_lb_var = tk.StringVar(value="1.5")
        self.f_lb_entry = add(ttk.Entry(top, textvariable=self.f_lb_var, width=5))

        self.f_x2_label = add(ttk.Label(top, text="换手率≥"))
        self.f_hs_var = tk.StringVar(value="3.0")
        self.f_hs_entry = add(ttk.Entry(top, textvariable=self.f_hs_var, width=5))
        self.f_x2_suffix = add(ttk.Label(top, text="%"))

        add(ttk.Label(top, text="排序"))
        self.sort_var = tk.StringVar(value="量比")
        self.screen_sort_combo = add(ttk.Combobox(
            top, textvariable=self.sort_var, width=8, state="readonly",
            values=("量比", "换手率", "涨跌幅", "昨涨幅", "涨幅差", "连涨",
                    "24h消息", "买入信号", "成交额", "开盘倾向")))

        self.screen_btn = add(ttk.Button(top, text="查询", style="Accent.TButton",
                                         command=self._run_screen), padx=6)
        self.screen_wencai_btn = add(ttk.Button(top, text="转问财",
                                                command=self._screen_to_wencai))
        add(ttk.Button(top, text="导出CSV", command=self._export_screen_csv))
        self.screen_count_var = tk.StringVar(value="点击「查询」开始筛选")
        add(ttk.Label(top, textvariable=self.screen_count_var, foreground=FG_MUTED),
            padx=(10, 0))

        # 第二行: 当日 vs 昨日 对比条件(量化筛股)
        top2 = ttk.Frame(self.tab_screen, padding=(8, 0))
        top2.pack(fill="x")
        ttk.Label(top2, text="昨日涨幅").pack(side="left")
        self.f_prev_min_var = tk.StringVar(value="")      # 留空 = 不限
        ttk.Entry(top2, textvariable=self.f_prev_min_var, width=5).pack(side="left")
        ttk.Label(top2, text="% ~ ").pack(side="left")
        self.f_prev_max_var = tk.StringVar(value="")
        ttk.Entry(top2, textvariable=self.f_prev_max_var, width=5).pack(side="left")
        ttk.Label(top2, text="%").pack(side="left")
        ttk.Label(top2, text="  连涨≥").pack(side="left")
        self.f_streak_var = tk.StringVar(value="")
        ttk.Entry(top2, textvariable=self.f_streak_var, width=4).pack(side="left")
        ttk.Label(top2, text="天(含今日)").pack(side="left")
        self.f_accel_var = tk.BooleanVar(value=False)
        ttk.Checkbutton(top2, text="仅看涨幅加速(今日>昨日)", variable=self.f_accel_var).pack(side="left", padx=10)
        self.f_news_var = tk.BooleanVar(value=False)
        ttk.Checkbutton(top2, text="仅看24h有利好", variable=self.f_news_var).pack(side="left", padx=4)
        self.f_signal_var = tk.BooleanVar(value=False)
        ttk.Checkbutton(top2, text="仅看买入候选(≥3项共振)", variable=self.f_signal_var).pack(side="left", padx=4)
        ttk.Label(top2, text="· 留空/不勾 = 不限", foreground=FG_MUTED).pack(side="left", padx=6)

        # 结果表格
        cols = ("code", "name", "industry", "price", "pct", "pct_prev", "delta", "streak",
                "news", "lb", "hs", "amount", "volume", "bias", "signal")
        headers = ("代码", "名称", "行业", "现价", "涨跌幅", "昨涨幅", "涨幅差", "连涨",
                   "24h消息", "量比", "换手率", "成交额", "成交量", "开盘倾向", "买入信号")
        widths = (72, 100, 88, 76, 76, 72, 72, 48, 104, 60, 72, 88, 88, 92, 84)
        self.screen_cols = cols
        self.screen_headers = dict(zip(cols, headers))
        tf = ttk.Frame(self.tab_screen, padding=(8, 4))
        tf.pack(fill="both", expand=True)
        self.stree = ttk.Treeview(tf, columns=cols, show="headings")
        for c, h, w in zip(cols, headers, widths):
            self.stree.heading(c, text=h, command=lambda col=c: self._sort_screen(col))
            self.stree.column(c, width=w, anchor="e")
        self.stree.column("name", anchor="w")
        self.stree.column("code", anchor="w")
        self.stree.column("industry", anchor="w")
        svsb = ttk.Scrollbar(tf, orient="vertical", command=self.stree.yview)
        self.stree.configure(yscrollcommand=svsb.set)
        self.stree.pack(side="left", fill="both", expand=True)
        svsb.pack(side="right", fill="y")
        self.stree.tag_configure("up", foreground=COLOR_UP_DEFAULT)
        self.stree.tag_configure("down", foreground=COLOR_DOWN_DEFAULT)
        self.stree.tag_configure("flat", foreground=COLOR_FLAT)
        # 买入候选行背景高亮(与涨跌前景色叠加: 多标签各管各的选项)
        self.stree.tag_configure("sig3", background="#3A2F0B", foreground=ACCENT_HOVER)   # 候选(3项共振)
        self.stree.tag_configure("sig4", background="#5E4E0C", foreground=ACCENT_HOVER)   # 强候选(4项)
        self.stree.bind("<Double-1>", self._open_screen_detail)
        self.stree.bind("<Button-3>", self._on_screen_right_click)

        # 分页栏
        pg = ttk.Frame(self.tab_screen, padding=(8, 4))
        pg.pack(fill="x")
        ttk.Button(pg, text="上一页", command=self._screen_prev).pack(side="left")
        self.page_var = tk.StringVar(value="第 1 / 1 页")
        ttk.Label(pg, textvariable=self.page_var, width=16).pack(side="left", padx=6)
        ttk.Button(pg, text="下一页", command=self._screen_next).pack(side="left")
        ttk.Label(pg, text="  每页").pack(side="left", padx=(16, 2))
        self.page_size_var = tk.StringVar(value="50")
        ttk.Combobox(pg, textvariable=self.page_size_var, width=5, state="readonly",
                     values=("20", "50", "100")).pack(side="left")
        self.page_size_var.trace_add("write", lambda *a: self._screen_page_size_changed())
        ttk.Label(pg, text="条   跳转:").pack(side="left", padx=4)
        self.goto_var = tk.StringVar()
        ttk.Entry(pg, textvariable=self.goto_var, width=5).pack(side="left")
        ttk.Button(pg, text="跳转", command=self._screen_goto).pack(side="left", padx=2)
        ttk.Label(pg, text="黄底=买入候选 · 条件(4项共振): 倾向≥60 / 涨幅加速 / 连涨≥2 / 24h无利空",
                  foreground=FG_MUTED).pack(side="left", padx=14)
        self._screen_market_changed()

    def _screen_market_changed(self):
        if not hasattr(self, "screen_market_var"):
            return
        m = {"A股": "a", "美股": "us", "ETF": "etf"}.get(
            self.screen_market_var.get(), "a")
        self.screen_market = m
        cfg = {
            "a": ("A股全市场选股", "   量比≥", "  换手率≥", "%", "1.5", "3.0"),
            "etf": ("ETF选股", "  成交额≥(亿)", "  换手率≥", "%", "1.0", "0.5"),
            "us": ("美股全市场选股", "  成交额≥(百万$)", "  市值≥(亿$)", "", "50", "100"),
        }[m]
        self.screen_title_var.set(cfg[0])
        self.f_x1_label.configure(text=cfg[1])
        self.f_x2_label.configure(text=cfg[2])
        self.f_x2_suffix.configure(text=cfg[3])
        self.f_lb_var.set(cfg[4])
        self.f_hs_var.set(cfg[5])
        self.screen_wencai_btn.configure(state="normal" if m == "a" else "disabled")
        vals = {
            "a": ("量比", "换手率", "涨跌幅", "昨涨幅", "涨幅差", "连涨",
                  "24h消息", "买入信号", "成交额", "开盘倾向"),
            "etf": ("成交额", "换手率", "涨跌幅", "昨涨幅", "涨幅差", "连涨",
                    "24h消息", "买入信号", "开盘倾向"),
            "us": ("涨跌幅", "成交额", "昨涨幅", "涨幅差", "连涨",
                   "24h消息", "买入信号", "开盘倾向"),
        }[m]
        self.screen_sort_combo.configure(values=vals)
        if self.sort_var.get() not in vals:
            self.sort_var.set(vals[0])
        self.screen_count_var.set("选择条件后点「查询」")

    def _run_screen(self):
        if self._screen_busy:
            return

        def opt_float(var):
            """可选数值过滤项: 留空返回 None(=不限)。"""
            s = (var.get() or "").strip()
            return float(s) if s else None
        try:
            f_min = float(self.f_min_var.get())
            f_max = float(self.f_max_var.get())
            x1 = float(self.f_lb_var.get())
            x2 = float(self.f_hs_var.get())
            p_min = opt_float(self.f_prev_min_var)
            p_max = opt_float(self.f_prev_max_var)
            st_min = opt_float(self.f_streak_var)
        except ValueError:
            messagebox.showwarning("参数错误", "请填写数字: 涨幅区间 / 筛选条件 / 昨日涨幅 / 连涨")
            return
        market = getattr(self, "screen_market", "a")
        if market == "a":
            lb_min, hs_min, amount_min, cap_min = x1, x2, 0, 0
        elif market == "etf":
            lb_min, hs_min, amount_min, cap_min = 0, x2, x1 * 1e8, 0
        else:
            lb_min, hs_min, amount_min, cap_min = 0, 0, x1 * 1e6, x2 * 1e8
        if f_min > f_max:
            f_min, f_max = f_max, f_min
        if p_min is not None and p_max is not None and p_min > p_max:
            p_min, p_max = p_max, p_min
        if st_min is not None:
            st_min = max(0, st_min)
        accel_only = self.f_accel_var.get()
        news_only = self.f_news_var.get()
        signal_only = self.f_signal_var.get()

        self._screen_busy = True
        self.screen_btn.configure(state="disabled")
        self.screen_count_var.set("筛选中, 请稍候...")

        sort_name = self.sort_var.get()

        def work():
            try:
                label = {"a": "A股", "us": "美股", "etf": "ETF"}.get(market, market)
                self._screen_queue.put(("status", f"正在抓取 {label} 行情..."))
                raw = fetch_screen_universe(market, f_min)
                # 第一段: 涨幅区间 + 市场对应的成交额/市值/换手率
                cands = []
                for r in raw:
                    cp = to_float(r.get("pct"))
                    if cp is None or not (f_min <= cp <= f_max):
                        continue
                    if amount_min and (r.get("amount") or 0) < amount_min:
                        continue
                    if cap_min and (r.get("market_cap") or 0) < cap_min:
                        continue
                    hs = to_float(r.get("turnover")) or 0.0
                    if hs_min and hs < hs_min:
                        continue
                    cands.append(r)
                # 第二段: A股/ETF 补齐量比/换手(带 TTL 缓存)
                if market in ("a", "etf") and cands:
                    self._screen_queue.put(("status",
                                            f"正在批量补齐量比... ({len(cands)} 只)"))
                    em_items = [(r.get("symbol"), em_quote_candidates(r.get("symbol")))
                                for r in cands]
                    em_quotes = fetch_em_quotes(em_items)
                    for r in cands:
                        q = em_quotes.get(r.get("symbol"))
                        if q:
                            if q.get("volume_ratio") is not None:
                                r["lb"] = q["volume_ratio"]
                            if q.get("turnover") is not None:
                                r["hs"] = q["turnover"]

                    def enrich(r):
                        if r.get("lb") is not None and r.get("hs") is not None:
                            return r
                        lb, hs = fetch_a_metrics(r.get("symbol"))
                        if lb is not None:
                            r["lb"] = lb
                        if hs is not None:
                            r["hs"] = hs
                        return r
                    missing = [r for r in cands
                               if r.get("lb") is None or r.get("hs") is None]
                    if missing:
                        with ThreadPoolExecutor(max_workers=24) as ex:
                            list(ex.map(enrich, missing))
                else:
                    for r in cands:
                        if r.get("lb") is None:
                            r["lb"] = 0.0
                        if r.get("hs") is None:
                            r["hs"] = to_float(r.get("turnover")) or 0.0
                # 第三段: 日K补齐「昨日」指标(昨涨幅/连涨/昨日量比, 当日缓存), 供对比过滤与打分
                self._screen_queue.put(("status",
                                        f"正在抓取日K对比昨涨幅... ({len(cands)} 只)"))

                def enrich_kline(r):
                    m = fetch_prev_metrics(r.get("symbol"))
                    if m:
                        r["pct_prev"] = m.get("p")
                        r["streak_base"] = m.get("s")
                        r["vr"] = m.get("vr")
                    return r
                if cands:
                    with ThreadPoolExecutor(max_workers=24) as ex:
                        cands = list(ex.map(enrich_kline, cands))
                # 第四段: 24h消息面(东财个股资讯, 利好/利空计数), 参与过滤与打分
                self._screen_queue.put(("status",
                                        f"正在抓取24h消息面... ({len(cands)} 只)"))

                def enrich_news(r):
                    sym = r.get("symbol") or ""
                    _items, stats = fetch_stock_news(sym[:2], sym[2:])
                    r["news_pos"] = stats.get("n_pos", 0)
                    r["news_neg"] = stats.get("n_neg", 0)
                    return r
                if cands:
                    with ThreadPoolExecutor(max_workers=24) as ex:
                        cands = list(ex.map(enrich_news, cands))
                # 组装行(含全部原始因子字段) + 当日 vs 昨日对比过滤, 暂不填开盘倾向
                rows = []
                for r in cands:
                    lb = to_float(r.get("lb")) or 0.0
                    if lb < lb_min:
                        continue
                    cp = to_float(r.get("pct"))
                    pp = r.get("pct_prev")
                    # 昨日涨幅区间过滤(启用该条件时, 数据缺失的直接排除)
                    if p_min is not None and (pp is None or pp < p_min):
                        continue
                    if p_max is not None and (pp is None or pp > p_max):
                        continue
                    delta = round(cp - pp, 2) if (cp is not None and pp is not None) else None
                    if accel_only and (delta is None or delta <= 0):
                        continue
                    streak = None
                    if r.get("streak_base") is not None:
                        streak = r["streak_base"] + 1 if (cp is not None and cp > 0) else 0
                    if st_min is not None and (streak is None or streak < st_min):
                        continue
                    n_pos = r.get("news_pos") or 0
                    n_neg = r.get("news_neg") or 0
                    if news_only and n_pos < 1:
                        continue
                    rows.append({
                        "code": r.get("code"), "name": r.get("name"),
                        "symbol": r.get("symbol"),
                        "price": to_float(r.get("price")),
                        "pct": cp,
                        "pct_prev": pp,
                        "delta": delta,
                        "streak": streak,
                        "vr": r.get("vr"),
                        "news_pos": n_pos,
                        "news_neg": n_neg,
                        "news_score": n_pos - n_neg,
                        "lb": lb,
                        "hs": to_float(r.get("hs")) or to_float(r.get("turnover")) or 0.0,
                        "amount": to_float(r.get("amount"), 0),
                        "volume": to_float(r.get("volume"), 0),
                        "high": to_float(r.get("high")),
                        "low": to_float(r.get("low")),
                        "industry": r.get("industry") or "…",
                        "market": r.get("market") or market,
                    })
                # 横截面多因子合成开盘倾向(分位排名 + 加权, 0~100)
                open_bias_composite(rows)
                # 买入候选信号: 4项多头条件共振计数, >=3 项黄底高亮
                for r in rows:
                    r["signal"] = buy_signal(r)
                if signal_only:
                    rows = [r for r in rows if r["signal"] >= SIGNAL_CAND]
                sort_key = {"量比": "lb", "换手率": "hs", "涨跌幅": "pct", "昨涨幅": "pct_prev",
                            "涨幅差": "delta", "连涨": "streak", "24h消息": "news_score",
                            "买入信号": "signal", "成交额": "amount", "开盘倾向": "bias"}
                key = sort_key.get(sort_name, "lb")
                rows.sort(key=lambda x: x.get(key) if x.get(key) is not None else -1e18, reverse=True)
                # 先显示(行业占位为 …)
                self._screen_queue.put(("deliver", rows, False))
                # 第三段: 补齐行业(带缓存), 完成后更新
                if rows:
                    def add_industry(row):
                        if row.get("market") in ("us", "etf") or                                 row.get("industry") not in ("", "…", None):
                            if not row.get("industry"):
                                row["industry"] = "—"
                            return row
                        row["industry"] = fetch_industry(row.get("symbol"))
                        return row
                    with ThreadPoolExecutor(max_workers=16) as ex:
                        rows = list(ex.map(add_industry, rows))
                self._screen_queue.put(("deliver", rows, True))
            except Exception as e:
                err = str(e)
                _LOG.exception("选股器查询失败")
                self._screen_queue.put(("deliver", [], True))
                self._screen_queue.put(("status", f"查询失败: {err}"))

        threading.Thread(target=work, daemon=True).start()

    def _screen_pump(self):
        try:
            while True:
                item = self._screen_queue.get_nowait()
                if item[0] == "status":
                    self.screen_count_var.set(item[1])
                elif item[0] == "deliver":
                    self._deliver(item[1], item[2])
        except queue.Empty:
            pass
        try:
            self.root.after(200, self._screen_pump)
        except Exception:
            pass

    def _deliver(self, rows, final):
        self.screen_rows = rows
        if self.screen_sort_col:
            self._apply_screen_sort()
        self.screen_page = 0
        self._render_screen_table()
        if final:
            self._screen_busy = False
            self.screen_btn.configure(state="normal")
            n_sig = sum(1 for r in rows if (r.get("signal") or 0) >= SIGNAL_CAND)
            n_strong = sum(1 for r in rows if (r.get("signal") or 0) >= SIGNAL_STRONG)
            self.screen_count_var.set(
                f"共筛出 {len(rows)} 只 · 买入候选 {n_sig} 只(黄底, 其中强候选 {n_strong})")
            _save_industry_cache()
            _save_kline_cache()
        else:
            self.screen_count_var.set(f"已筛出 {len(rows)} 只, 正在补齐行业...")

    def _total_pages(self):
        if not self.screen_rows:
            return 1
        return max(1, (len(self.screen_rows) + self.screen_page_size - 1) // self.screen_page_size)

    def _render_screen_table(self):
        self.stree.delete(*self.stree.get_children())
        pages = self._total_pages()
        self.screen_page = max(0, min(self.screen_page, pages - 1))
        start = self.screen_page * self.screen_page_size
        chunk = self.screen_rows[start:start + self.screen_page_size]
        for r in chunk:
            label = r.get("bias_label") or "中性"
            bias_tag = "up" if label == "高开" else ("down" if label == "低开" else "flat")
            sig = r.get("signal") or 0
            # 信号>=3 加黄底标签(背景), 与涨跌前景色标签叠加
            tags = ((f"sig{sig}",) if sig >= SIGNAL_CAND else ()) + (bias_tag,)
            score = r.get("bias")
            bias_text = "--" if score is None else f"{label} {score:d}"
            vals = (
                r["code"],
                r["name"] or "",
                r.get("industry") or "—",
                fmt_price(r.get("price")),
                fmt_pct(r.get("pct")),
                fmt_pct(r.get("pct_prev")),
                fmt_pct(r.get("delta")),
                "--" if r.get("streak") is None else f"{r['streak']}",
                fmt_news(r),
                fmt_price(r.get("lb")),
                fmt_pct_plain(r.get("hs")),
                fmt_amount(r.get("amount")),
                fmt_vol(r.get("volume")),
                bias_text,
                "★" * sig,
            )
            self.stree.insert("", "end", values=vals, tags=tags)
        self.page_var.set(f"第 {self.screen_page + 1} / {pages} 页")

    def _export_screen_csv(self):
        rows = getattr(self, "screen_rows", [])
        if not rows:
            messagebox.showinfo("导出", "当前没有筛选结果，请先查询", parent=self.root)
            return
        headers = ["代码", "名称", "行业", "现价", "涨跌幅%", "昨涨幅%", "涨幅差",
                   "连涨", "24h利好", "24h利空", "量比", "换手率%", "成交额",
                   "成交量", "开盘倾向", "倾向标签", "买入信号"]
        data = [[
            r.get("code"), r.get("name"), r.get("industry"),
            r.get("price"), r.get("pct"), r.get("pct_prev"), r.get("delta"),
            r.get("streak"), r.get("news_pos"), r.get("news_neg"),
            r.get("lb"), r.get("hs"), r.get("amount"), r.get("volume"),
            r.get("bias"), r.get("bias_label"), r.get("signal"),
        ] for r in rows]
        mkt = {"a": "A股", "us": "美股", "etf": "ETF"}.get(
            getattr(self, "screen_market", "a"), "a")
        path = export_rows_csv(
            self.root, "导出选股结果",
            f"screen_{mkt}_{time.strftime('%Y%m%d_%H%M')}.csv", headers, data)
        if path:
            self.screen_count_var.set(f"已导出 {len(data)} 行 → {path}")

    def _screen_sort_value(self, r, col):
        """选股器行某列的可排序值; None 表示缺失(排最后)。"""
        if col == "news":
            return r.get("news_score")
        if col in ("price", "pct", "pct_prev", "delta", "streak", "lb", "hs", "amount",
                   "volume", "bias", "signal"):
            return r.get(col)
        return r.get(col) or ""

    def _apply_screen_sort(self):
        col = self.screen_sort_col
        if not col or not self.screen_rows:
            return
        keyed = [(self._screen_sort_value(r, col), r) for r in self.screen_rows]
        present = [(v, r) for v, r in keyed if v is not None]
        missing = [r for v, r in keyed if v is None]
        present.sort(key=lambda t: t[0], reverse=self.screen_sort_desc)
        self.screen_rows = [r for _v, r in present] + missing

    def _update_screen_headings(self):
        for c in self.screen_cols:
            base = self.screen_headers[c]
            if c == self.screen_sort_col:
                self.stree.heading(c, text=base + (" ▼" if self.screen_sort_desc else " ▲"))
            else:
                self.stree.heading(c, text=base)

    def _sort_screen(self, col):
        if self.screen_sort_col == col:
            self.screen_sort_desc = not self.screen_sort_desc
        else:
            self.screen_sort_col = col
            self.screen_sort_desc = False
        self._apply_screen_sort()
        self.screen_page = 0
        self._update_screen_headings()
        self._render_screen_table()

    def _screen_prev(self):
        if self.screen_page > 0:
            self.screen_page -= 1
            self._render_screen_table()

    def _screen_next(self):
        if self.screen_page < self._total_pages() - 1:
            self.screen_page += 1
            self._render_screen_table()

    def _screen_goto(self):
        try:
            p = int(self.goto_var.get())
        except ValueError:
            return
        pages = self._total_pages()
        self.screen_page = max(0, min(p - 1, pages - 1))
        self.goto_var.set("")
        self._render_screen_table()

    def _screen_page_size_changed(self):
        try:
            self.screen_page_size = int(self.page_size_var.get())
        except ValueError:
            self.screen_page_size = 50
        self.screen_page = 0
        self._render_screen_table()

    def _open_screen_detail(self, _event):
        sel = self.stree.selection()
        if not sel:
            return
        code = self.stree.item(sel[0], "values")[0]
        sym = ""
        for r in self.screen_rows:
            if r["code"] == code:
                sym = r.get("symbol", "")
                break
        webbrowser.open(f"https://gu.qq.com/{sym}" if sym else f"https://gu.qq.com/{code}")

    # ---------------- 排序(自选盯盘表头) ----------------
    def _sort_watch(self, col):
        if self.watch_sort_col == col:
            self.watch_sort_desc = not self.watch_sort_desc
        else:
            self.watch_sort_col = col
            self.watch_sort_desc = False
        self._update_watch_headings()
        self._render_table()

    def _watch_sort_value(self, sym, col):
        """返回该列可排序值; None 表示缺失(固定排最后)。"""
        entry = self.stock_results.get(sym)
        if not entry or entry[0] is None:
            return None
        d = entry[0]
        if col in WATCH_NUMERIC_COLS:
            return d.get(col)
        if col == "code":
            return sym
        if col == "name":
            return d.get("name") or None
        if col == "mkt":
            c = classify_symbol(sym)
            return c[2] if c else None
        if col == "time":
            return d.get("time") or None
        return None

    def _sorted_watch(self, syms):
        col = self.watch_sort_col
        desc = self.watch_sort_desc
        vals = {s: self._watch_sort_value(s, col) for s in syms}
        present = [(s, vals[s]) for s in syms if vals[s] is not None]
        missing = [s for s in syms if vals[s] is None]
        present.sort(key=lambda t: t[1], reverse=desc)
        return [s for s, _v in present] + missing

    def _update_watch_headings(self):
        for c in self.watch_cols:
            base = self.watch_headers[c]
            if c == self.watch_sort_col:
                self.tree.heading(c, text=base + (" ▼" if self.watch_sort_desc else " ▲"))
            else:
                self.tree.heading(c, text=base)

    # ---------------- 右键菜单: 复制代码 / 公告消息 ----------------
    def _copy_code(self, code):
        self.root.clipboard_clear()
        self.root.clipboard_append(code)
        self.root.update()

    def _show_context_menu(self, event, code):
        menu = tk.Menu(self.root, tearoff=0, bg=BG_CARD, fg=FG_TEXT,
                       activebackground=BG_HOVER, activeforeground=ACCENT,
                       bd=0, relief="flat")
        menu.add_command(label=f"复制代码 {code}", command=lambda: self._copy_code(code))
        menu.add_command(label="查看分笔成交", command=lambda: self._open_ticks(code))
        menu.add_command(label="综合评分/买入区间", command=lambda: self._open_evaluation(code))
        c = classify_symbol(code)
        mkt = c[2] if c else ""
        if mkt == "cr":
            menu.add_command(label="打开 Binance 行情",
                             command=lambda: webbrowser.open(detail_url("cr", c[1])))
        else:
            menu.add_command(label="查看24h资讯", command=lambda: self._open_news24(code))
            if mkt in ("sh", "sz", "bj"):
                menu.add_command(label="查看公告消息", command=lambda: self._open_news(code))
        self._popup = menu
        try:
            menu.tk_popup(event.x_root, event.y_root)
        finally:
            menu.grab_release()

    def _on_watch_right_click(self, event):
        row = self.tree.identify_row(event.y)
        if not row:
            return
        self.tree.selection_set(row)
        code = self.tree.item(row, "values")[1]
        self._show_context_menu(event, code)

    def _on_screen_right_click(self, event):
        row = self.stree.identify_row(event.y)
        if not row:
            return
        self.stree.selection_set(row)
        code = self.stree.item(row, "values")[0]
        self._show_context_menu(event, code)

    # ---------------- 综合评估弹窗 ----------------
    def _open_evaluation(self, code):
        c = classify_symbol(code)
        if not c:
            return
        quote = None
        entry = self.stock_results.get(code)
        if entry:
            quote = entry[0]
        factor_row = None
        for r in self.factor_rows:
            if r.get("symbol") == c[0] or (r.get("code") == c[1]
                                           and r.get("market") in (None, self.factor_market)):
                factor_row = r
                break

        win = tk.Toplevel(self.root)
        win.configure(bg=BG_ROOT)
        win.title(f"综合评估 - {c[1]}")
        win.geometry("780x700")
        win.transient(self.root)

        hdr = ttk.Frame(win, padding=(8, 6))
        hdr.pack(fill="x")
        ttk.Label(hdr, text=f"{c[1]} 综合评估",
                  font=("Microsoft YaHei", 11, "bold")).pack(side="left")
        status_var = tk.StringVar(value="分析中...")
        ttk.Label(hdr, textvariable=status_var, foreground=FG_MUTED).pack(side="right")

        tf = ttk.Frame(win, padding=(8, 4))
        tf.pack(fill="both", expand=True)
        text = tk.Text(tf, wrap="word", font=("Microsoft YaHei", 9),
                       background=BG_PANEL, foreground=FG_TEXT, insertbackground=FG_TEXT,
                       relief="flat", padx=10, pady=8, selectbackground=ACCENT,
                       selectforeground=BG_ROOT)
        vsb = ttk.Scrollbar(tf, orient="vertical", command=text.yview)
        text.configure(yscrollcommand=vsb.set)
        text.pack(side="left", fill="both", expand=True)
        vsb.pack(side="right", fill="y")
        text.tag_configure("h", font=("Microsoft YaHei", 11, "bold"), spacing1=10, spacing3=4)
        text.tag_configure("buy", foreground=COLOR_UP_DEFAULT)
        text.tag_configure("sell", foreground=COLOR_DOWN_DEFAULT)
        text.tag_configure("warn", foreground=ACCENT)
        text.tag_configure("muted", foreground=FG_MUTED)
        text.configure(state="disabled")

        btns = ttk.Frame(win, padding=(8, 4))
        btns.pack(fill="x")
        refresh_btn = ttk.Button(btns, text="重新评估")
        refresh_btn.pack(side="left")
        copy_btn = ttk.Button(btns, text="复制报告",
                              command=lambda: self._copy_text(text.get("1.0", "end").strip()))
        copy_btn.pack(side="left", padx=6)
        ttk.Label(btns, text="研究参考，不构成投资建议", foreground=FG_MUTED).pack(side="right")

        q = queue.Queue()
        state = {"closed": False, "busy": False, "pump": None}

        def render(ev, lines):
            if state["closed"]:
                return
            text.configure(state="normal")
            text.delete("1.0", "end")
            for tag, line in lines:
                text.insert("end", line + "\n", tag)
            text.configure(state="disabled")
            if ev.get("error"):
                status_var.set(ev["error"])
            else:
                status_var.set(f"评分 {ev['score']}/100 · {ev['label']} · "
                               f"{time.strftime('%H:%M:%S')}")
            state["busy"] = False
            refresh_btn.configure(state="normal")

        def pump():
            if state["closed"]:
                return
            try:
                while True:
                    ev, lines = q.get_nowait()
                    render(ev, lines)
            except queue.Empty:
                pass
            state["pump"] = win.after(200, pump)

        def run():
            if state["busy"]:
                return
            state["busy"] = True
            refresh_btn.configure(state="disabled")
            status_var.set("分析中...")

            def work():
                try:
                    ev = collect_evaluation(code, quote=quote, factor_row=factor_row)
                    q.put((ev, format_evaluation(ev)))
                except Exception as e:
                    q.put(({"error": f"评估失败: {e}"}, [("warn", f"评估失败: {e}")]))

            threading.Thread(target=work, daemon=True).start()

        def close():
            state["closed"] = True
            aid = state.get("pump")
            if aid:
                try:
                    win.after_cancel(aid)
                except Exception:
                    pass
            win.destroy()

        refresh_btn.configure(command=run)
        win.protocol("WM_DELETE_WINDOW", close)
        pump()
        run()

    def _copy_text(self, value):
        self.root.clipboard_clear()
        self.root.clipboard_append(value)
        self.root.update()

    # ---------------- 分笔成交弹窗 ----------------
    def _open_ticks(self, code):
        c = classify_symbol(code)
        if not c:
            return
        _tcode, disp, _mkt = c
        pf = fmt_crypto_price if _mkt == "cr" else fmt_price
        win = tk.Toplevel(self.root)
        win.configure(bg=BG_ROOT)
        win.title(f"分笔/分时 - {disp}")
        win.geometry("620x560")
        win.transient(self.root)

        hdr = ttk.Frame(win, padding=(8, 6))
        hdr.pack(fill="x")
        ttk.Label(hdr, text=f"{disp} 分笔/分时 · 自动刷新 5 秒",
                  font=("Microsoft YaHei", 10, "bold")).pack(side="left")
        source_var = tk.StringVar(value="加载中...")
        ttk.Label(hdr, textvariable=source_var, foreground=FG_MUTED).pack(side="right")

        cols = ("time", "price", "volume", "direction")
        headers = ("时间", "价格", "量", "方向")
        widths = (120, 100, 100, 70)
        tf = ttk.Frame(win, padding=(8, 4))
        tf.pack(fill="both", expand=True)
        tree = ttk.Treeview(tf, columns=cols, show="headings")
        for col, h, w in zip(cols, headers, widths):
            tree.heading(col, text=h)
            tree.column(col, width=w, anchor="e")
        tree.column("time", anchor="w")
        vsb = ttk.Scrollbar(tf, orient="vertical", command=tree.yview)
        tree.configure(yscrollcommand=vsb.set)
        tree.pack(side="left", fill="both", expand=True)
        vsb.pack(side="right", fill="y")
        tree.tag_configure("buy", foreground=COLOR_UP_DEFAULT)
        tree.tag_configure("sell", foreground=COLOR_DOWN_DEFAULT)
        tree.tag_configure("flat", foreground=COLOR_FLAT)
        ttk.Label(win, text="量为数据源原始单位（A股通常为手）；仅作行情参考，不构成投资建议",
                  foreground=FG_MUTED).pack(anchor="w", padx=10, pady=(0, 6))

        state = {"closed": False, "after": None, "pump": None}
        tick_q = queue.Queue()

        def render(rows, src):
            if state["closed"]:
                return
            if rows:
                tree.delete(*tree.get_children())
                for r in rows[-300:]:
                    d = r.get("direction") or "中性"
                    tag = "buy" if d == "买" else ("sell" if d == "卖" else "flat")
                    tree.insert("", "end", values=(
                        r.get("time") or "", pf(r.get("price")),
                        fmt_vol(r.get("volume")), d), tags=(tag,))
                source_var.set(f"数据源: {src or '—'} · {len(rows)} 笔 · "
                               f"刷新 {time.strftime('%H:%M:%S')}")
            else:
                source_var.set(f"暂无数据/重试中 · {time.strftime('%H:%M:%S')}")

        def pump():
            if state["closed"]:
                return
            try:
                while True:
                    rows, src = tick_q.get_nowait()
                    render(rows, src)
            except queue.Empty:
                pass
            state["pump"] = win.after(200, pump)

        def refresh():
            if state["closed"]:
                return

            def work():
                rows, src = fetch_ticks(code, 50)
                tick_q.put((rows, src))

            threading.Thread(target=work, daemon=True).start()
            state["after"] = win.after(5000, refresh)

        def close():
            state["closed"] = True
            for key in ("after", "pump"):
                aid = state.get(key)
                if aid:
                    try:
                        win.after_cancel(aid)
                    except Exception:
                        pass
            win.destroy()

        win.protocol("WM_DELETE_WINDOW", close)
        pump()
        refresh()

    # ---------------- 公告消息弹窗 ----------------
    def _open_news(self, code):
        c = classify_symbol(code)
        mkt = c[2] if c else ""
        if mkt not in ("sh", "sz", "bj"):
            messagebox.showinfo("提示", "公告消息当前仅支持 A股。\n"
                                "(数据源为东方财富, 港股/美股无对应公告)")
            return
        disp = c[1]

        win = tk.Toplevel(self.root)
        win.configure(bg=BG_ROOT)
        win.title(f"公告消息 - {disp}")
        win.geometry("760x540")
        win.transient(self.root)

        hdr = ttk.Frame(win, padding=(8, 6))
        hdr.pack(fill="x")
        ttk.Label(hdr, text=f"{disp} 基本面公告 · 利好/利空为关键词启发式标注",
                  font=("Microsoft YaHei", 10, "bold")).pack(side="left")
        status = tk.StringVar(value="加载中...")
        ttk.Label(hdr, textvariable=status, foreground=FG_MUTED).pack(side="right")

        tf = ttk.Frame(win, padding=(8, 4))
        tf.pack(fill="both", expand=True)
        cols = ("date", "impact", "title", "art")
        headers = {"date": "日期", "impact": "影响", "title": "公告标题"}
        tree = ttk.Treeview(tf, columns=cols, show="headings")
        for c in ("date", "impact", "title"):
            tree.heading(c, text=headers[c], command=lambda col=c: sort(col))
        tree.column("date", width=90, anchor="center")
        tree.column("impact", width=56, anchor="center")
        tree.column("title", width=580, anchor="w")
        tree.column("art", width=0, stretch=False)
        vsb = ttk.Scrollbar(tf, orient="vertical", command=tree.yview)
        tree.configure(yscrollcommand=vsb.set)
        tree.pack(side="left", fill="both", expand=True)
        vsb.pack(side="right", fill="y")
        tree.tag_configure("利好", foreground=COLOR_UP_DEFAULT)
        tree.tag_configure("利空", foreground=COLOR_DOWN_DEFAULT)
        tree.tag_configure("中性", foreground=COLOR_FLAT)
        tree.bind("<Double-1>", lambda e: self._open_announce_detail(tree, disp))

        holder = {"rows": []}
        sort_state = {"col": None, "desc": False}
        impact_order = {"利好": 0, "中性": 1, "利空": 2}

        def sort_value(r, col):
            if col == "date":
                return r["date"]
            if col == "impact":
                return impact_order.get(r["impact"], 1)
            return r["title"]

        def render():
            tree.delete(*tree.get_children())
            for r in holder["rows"]:
                tree.insert("", "end",
                            values=(r["date"], r["impact"], r["title"], r["art_code"]),
                            tags=(r["impact"],))

        def sort(col):
            if sort_state["col"] == col:
                sort_state["desc"] = not sort_state["desc"]
            else:
                sort_state["col"] = col
                sort_state["desc"] = False
            holder["rows"].sort(key=lambda r: sort_value(r, sort_state["col"]),
                                reverse=sort_state["desc"])
            render()
            for c in ("date", "impact", "title"):
                mark = ""
                if sort_state["col"] == c:
                    mark = " ▼" if sort_state["desc"] else " ▲"
                tree.heading(c, text=headers[c] + mark)

        def work():
            try:
                rows = fetch_announcements(disp)
                err = None
            except Exception as ex:
                rows, err = [], str(ex)

            def update_ui():
                if err:
                    status.set(f"加载失败: {err}")
                    return
                holder["rows"] = rows
                render()
                n_pos = sum(1 for r in rows if r["impact"] == "利好")
                n_neg = sum(1 for r in rows if r["impact"] == "利空")
                status.set(f"共 {len(rows)} 条 · 利好 {n_pos} · 利空 {n_neg} · 双击查看详情")
            win.after(0, update_ui)

        threading.Thread(target=work, daemon=True).start()

    def _open_announce_detail(self, tree, code):
        sel = tree.selection()
        if not sel:
            return
        art = tree.item(sel[0], "values")[3]
        if art:
            webbrowser.open(ANNOUNCE_DETAIL.format(code=code, art_code=art))

    # ---------------- 24h消息面弹窗(三市场) ----------------
    def _open_news24(self, code):
        """24h消息面弹窗: 东财个股资讯, 仅展示近24小时, 利好/利空关键词标注。"""
        c = classify_symbol(code)
        if not c:
            return
        _tcode, disp, mkt = c
        qt_code = ""
        entry = self.stock_results.get(code)     # 自选盯盘行情里有美股完整代码(如 AAPL.OQ)
        if entry and entry[0]:
            qt_code = entry[0].get("qt_code") or ""

        win = tk.Toplevel(self.root)
        win.configure(bg=BG_ROOT)
        win.title(f"24h消息面 - {disp}")
        win.geometry("880x560")
        win.transient(self.root)

        hdr = ttk.Frame(win, padding=(8, 6))
        hdr.pack(fill="x")
        ttk.Label(hdr, text=f"{disp} 近24小时资讯 · 利好/利空为关键词启发式标注",
                  font=("Microsoft YaHei", 10, "bold")).pack(side="left")
        status = tk.StringVar(value="加载中...")
        ttk.Label(hdr, textvariable=status, foreground=FG_MUTED).pack(side="right")

        tf = ttk.Frame(win, padding=(8, 4))
        tf.pack(fill="both", expand=True)
        cols = ("time", "impact", "title", "url")
        headers = {"time": "时间", "impact": "影响", "title": "标题"}
        tree = ttk.Treeview(tf, columns=cols, show="headings")
        for cname in ("time", "impact", "title"):
            tree.heading(cname, text=headers[cname])
        tree.column("time", width=96, anchor="center")
        tree.column("impact", width=56, anchor="center")
        tree.column("title", width=660, anchor="w")
        tree.column("url", width=0, stretch=False)
        vsb = ttk.Scrollbar(tf, orient="vertical", command=tree.yview)
        tree.configure(yscrollcommand=vsb.set)
        tree.pack(side="left", fill="both", expand=True)
        vsb.pack(side="right", fill="y")
        tree.tag_configure("利好", foreground=COLOR_UP_DEFAULT)
        tree.tag_configure("利空", foreground=COLOR_DOWN_DEFAULT)
        tree.tag_configure("中性", foreground=COLOR_FLAT)
        tree.bind("<Double-1>", lambda e: self._open_url_from_tree(tree, 3))

        def work():
            try:
                items, stats = fetch_stock_news(mkt, disp, qt_code, size=50)
                err = None
            except Exception as ex:
                items, stats, err = [], {"n_pos": 0, "n_neg": 0}, str(ex)

            def update_ui():
                if err:
                    status.set(f"加载失败: {err}")
                    return
                for it in items:
                    tree.insert("", "end", values=(it["time"], it["impact"], it["title"], it["url"]),
                                tags=(it["impact"],))
                if items:
                    status.set(f"共 {len(items)} 条 · 利好 {stats['n_pos']} · "
                               f"利空 {stats['n_neg']} · 双击打开原文")
                else:
                    status.set("近24小时无资讯")
            win.after(0, update_ui)

        threading.Thread(target=work, daemon=True).start()

    def _open_url_from_tree(self, tree, idx):
        sel = tree.selection()
        if not sel:
            return
        url = tree.item(sel[0], "values")[idx]
        if url:
            webbrowser.open(url)

    # ================ 综合评估 ================
    def _build_eval_tab(self):
        top = ttk.Frame(self.tab_eval, padding=(8, 6))
        top.pack(fill="x")
        ttk.Label(top, text="综合评估", font=("Microsoft YaHei", 11, "bold")).pack(side="left")
        ttk.Label(top, text="  代码").pack(side="left")
        self.eval_code_var = tk.StringVar(value=self._eval_last_code or "600519")
        ent = ttk.Entry(top, textvariable=self.eval_code_var, width=14)
        ent.pack(side="left", padx=2)
        ent.bind("<Return>", lambda e: self._run_eval_tab())
        self.eval_btn = ttk.Button(top, text="评估", command=self._run_eval_tab,
                                   style="Accent.TButton")
        self.eval_btn.pack(side="left", padx=6)
        ttk.Button(top, text="复制报告", command=self._copy_eval_report).pack(side="left", padx=2)
        for code in ("AAPL", "600519", "510300", "BTC"):
            ttk.Button(top, text=code, width=7,
                       command=lambda c=code: self._eval_example(c)).pack(side="left", padx=1)
        self.eval_status_var = tk.StringVar(
            value="支持 美股 / A股 / 港股 / ETF / 加密货币；输入代码后回车或点评估")
        ttk.Label(self.tab_eval, textvariable=self.eval_status_var,
                  foreground=FG_MUTED, padding=(8, 2)).pack(fill="x")

        tf = ttk.Frame(self.tab_eval, padding=(8, 4))
        tf.pack(fill="both", expand=True)
        self.eval_text = tk.Text(tf, wrap="word", font=("Microsoft YaHei", 9),
                                 background=BG_PANEL, foreground=FG_TEXT, insertbackground=FG_TEXT,
                                 relief="flat", padx=12, pady=10,
                                 selectbackground=ACCENT, selectforeground=BG_ROOT)
        vsb = ttk.Scrollbar(tf, orient="vertical", command=self.eval_text.yview)
        self.eval_text.configure(yscrollcommand=vsb.set)
        self.eval_text.pack(side="left", fill="both", expand=True)
        vsb.pack(side="right", fill="y")
        self.eval_text.tag_configure("h", font=("Microsoft YaHei", 11, "bold"),
                                     spacing1=12, spacing3=4)
        self.eval_text.tag_configure("buy", foreground=COLOR_UP_DEFAULT)
        self.eval_text.tag_configure("sell", foreground=COLOR_DOWN_DEFAULT)
        self.eval_text.tag_configure("warn", foreground=ACCENT)
        self.eval_text.tag_configure("muted", foreground=FG_MUTED)
        self.eval_text.configure(state="disabled")
        if self._eval_last_lines:
            self._render_eval_tab_lines(self._eval_last_lines)

    def _eval_example(self, code):
        self.eval_code_var.set(code)
        self._run_eval_tab()

    def _run_eval_tab(self):
        if self._eval_busy:
            return
        code = self.eval_code_var.get().strip()
        c = classify_symbol(code)
        if not c:
            messagebox.showinfo("提示", "无法识别该代码，示例：AAPL / 600519 / 510300 / BTC / cr:PEPE")
            return
        quote = self.stock_results.get(code) or self.stock_results.get(c[1])
        quote = quote[0] if quote else None
        factor_row = None
        for r in self.factor_rows:
            if r.get("symbol") == c[0] or r.get("code") == c[1]:
                factor_row = r
                break
        self._eval_busy = True
        self.eval_btn.configure(state="disabled")
        self.eval_status_var.set(f"正在评估 {code} ...")

        def work():
            try:
                ev = collect_evaluation(code, quote=quote, factor_row=factor_row)
                self._eval_queue.put(("ok", ev, format_evaluation(ev)))
            except Exception as e:
                self._eval_queue.put(("err", str(e), None))

        threading.Thread(target=work, daemon=True).start()

    def _eval_pump(self):
        try:
            while True:
                kind, ev, lines = self._eval_queue.get_nowait()
                if kind == "ok":
                    self._eval_last_code = ev.get("code") or self.eval_code_var.get()
                    self._eval_last_report = "\n".join(line for _tag, line in lines)
                    self._eval_last_lines = lines
                    self._render_eval_tab_lines(lines)
                    self.eval_status_var.set(
                        f"{ev.get('name')} · 评分 {ev.get('score')}/100 · {ev.get('label')} · "
                        f"{time.strftime('%H:%M:%S')}")
                else:
                    self.eval_status_var.set(f"评估失败: {ev}")
                self._eval_busy = False
                self.eval_btn.configure(state="normal")
        except queue.Empty:
            pass
        try:
            self.root.after(250, self._eval_pump)
        except Exception:
            pass

    def _render_eval_tab_lines(self, lines):
        self.eval_text.configure(state="normal")
        self.eval_text.delete("1.0", "end")
        for tag, line in lines:
            self.eval_text.insert("end", line + "\n", tag)
        self.eval_text.configure(state="disabled")

    def _copy_eval_report(self):
        if not self._eval_last_report:
            return
        self._copy_text(self._eval_last_report)

    # ================ 因子选股 ================
    def _build_factor_tab(self):
        top = FlowFrame(self.tab_factor, padding=(8, 6))
        top.pack(fill="x")
        add = top.add

        add(ttk.Label(top, text="因子选股",
                      font=("Microsoft YaHei", 11, "bold")), padx=(0, 8))
        add(ttk.Label(top, text="市场"))
        self.factor_market_var = tk.StringVar(
            value={"a": "个股", "etf": "ETF", "crypto": "加密货币",
                   "us": "美股", "all": "个股+ETF"}.get(
                getattr(self, "factor_market", "all"), "个股+ETF"))
        add(ttk.Combobox(top, textvariable=self.factor_market_var, width=8,
                         state="readonly",
                         values=("个股+ETF", "个股", "ETF", "美股", "加密货币")))
        self.factor_market_var.trace_add("write", lambda *a: self._factor_market_changed())
        add(ttk.Label(top, text="池(成交额前)"))
        self.factor_limit_var = tk.StringVar(value=str(self.factor_limit))
        add(ttk.Combobox(top, textvariable=self.factor_limit_var, width=6,
                         state="readonly", values=("150", "300", "500")))
        add(ttk.Label(top, text="回看"))
        self.factor_lookback_var = tk.StringVar(value=str(self.factor_lookback))
        add(ttk.Combobox(top, textvariable=self.factor_lookback_var, width=6,
                         state="readonly", values=("120", "250")))
        add(ttk.Label(top, text="预测"))
        self.factor_horizon_var = tk.StringVar(value=str(self.factor_horizon))
        add(ttk.Combobox(top, textvariable=self.factor_horizon_var, width=4,
                         state="readonly", values=("1", "5")))
        add(ttk.Label(top, text="日"))
        self.factor_exclude_st_var = tk.BooleanVar(value=self.factor_exclude_st)
        self.factor_st_chk = add(ttk.Checkbutton(top, text="排除ST",
                                                 variable=self.factor_exclude_st_var))
        self.factor_exclude_limit_var = tk.BooleanVar(value=self.factor_exclude_limit)
        self.factor_limit_chk = add(ttk.Checkbutton(top, text="排除涨停",
                                                    variable=self.factor_exclude_limit_var))
        self.factor_buy_only_var = tk.BooleanVar(value=False)
        add(ttk.Checkbutton(top, text="仅看买入候选",
                            variable=self.factor_buy_only_var))
        add(ttk.Label(top, text="MA"))
        self.factor_ma_var = tk.StringVar(value=getattr(self, "factor_ma", "全部"))
        add(ttk.Combobox(top, textvariable=self.factor_ma_var, width=10,
                         state="readonly",
                         values=("全部", "站上MA5", "跌破MA5", "站上MA10", "跌破MA10",
                                 "站上MA20", "跌破MA20", "站上MA60", "跌破MA60")))
        self.factor_ma_var.trace_add("write", lambda *a: self._factor_ma_changed())
        add(ttk.Label(top, text="量/前2日"))
        self.factor_vol_var = tk.StringVar(value=getattr(self, "factor_vol", "全部"))
        add(ttk.Combobox(top, textvariable=self.factor_vol_var, width=12,
                         state="readonly",
                         values=("全部", "≈1倍(0.8~1.2)", "0.5~1.5倍",
                                 "放量≥1.5倍", "放量≥2倍", "放量≥3倍",
                                 "缩量≤0.8倍")))
        self.factor_vol_var.trace_add("write", lambda *a: self._factor_vol_changed())
        add(ttk.Label(top, text="得分≥"))
        self.factor_threshold_var = tk.StringVar(value=f"{self.factor_threshold:g}")
        add(ttk.Entry(top, textvariable=self.factor_threshold_var, width=5))
        self.factor_run_btn = add(ttk.Button(top, text="运行", style="Accent.TButton",
                                             command=self._run_factor), padx=6)
        self.factor_cancel_btn = add(ttk.Button(top, text="取消",
                                                command=self._factor_cancel_cmd,
                                                state="disabled"))
        add(ttk.Button(top, text="评价选中", command=self._eval_selected_factor))
        add(ttk.Button(top, text="量能回测", command=self._show_volume_analysis))
        add(ttk.Button(top, text="导出CSV", command=self._export_factor_csv))

        info = ttk.Frame(self.tab_factor, padding=(8, 0))
        info.pack(fill="x")
        self.factor_status_var = tk.StringVar(
            value="点击「运行」: 抓取成交额前 N 只日K, 计算 RankIC/ICIR 并做样本外检验")
        ttk.Label(info, textvariable=self.factor_status_var, foreground=FG_MUTED).pack(side="left")
        ttk.Label(info, text="次日建议为研究候选 · 样本外证据不足时自动降级 · 不构成投资建议",
                  foreground=FG_MUTED).pack(side="right")

        paned = ttk.Panedwindow(self.tab_factor, orient="vertical")
        paned.pack(fill="both", expand=True, padx=8, pady=(4, 6))

        sf = ttk.LabelFrame(paned, text="因子有效性 (RankIC / ICIR / 样本外)", padding=(4, 2))
        fcols = ("name", "category", "mean_ic", "icir", "t", "coverage",
                 "recent_ic", "win_rate", "direction", "weight", "status")
        fheaders = ("因子", "类别", "平均IC", "ICIR", "t值", "覆盖率",
                    "近20日IC", "IC胜率", "方向", "权重", "状态")
        fwidths = (150, 62, 66, 58, 52, 58, 68, 60, 50, 58, 190)
        self.factor_stat_cols = fcols
        self.factor_stat_headers = dict(zip(fcols, fheaders))
        self.fstats_tree = ttk.Treeview(sf, columns=fcols, show="headings", height=8)
        for c, h, w in zip(fcols, fheaders, fwidths):
            self.fstats_tree.heading(c, text=h, command=lambda col=c: self._sort_factor_stats(col))
            self.fstats_tree.column(c, width=w, anchor="e")
        for c in ("name", "category", "status"):
            self.fstats_tree.column(c, anchor="w")
        fsb = ttk.Scrollbar(sf, orient="vertical", command=self.fstats_tree.yview)
        self.fstats_tree.configure(yscrollcommand=fsb.set)
        self.fstats_tree.pack(side="left", fill="both", expand=True)
        fsb.pack(side="right", fill="y")
        self.fstats_tree.tag_configure("sel", background="#123A2A")
        self.fstats_tree.tag_configure("off", foreground=FG_MUTED)
        paned.add(sf, weight=1)

        rf = ttk.LabelFrame(paned, text="筛选结果 (按因子得分排序)", padding=(4, 2))
        rf_top = ttk.Frame(rf)
        rf_top.pack(fill="x")
        ttk.Label(rf_top, text="显示前").pack(side="left")
        self.factor_show_var = tk.StringVar(value=str(self.factor_show_n))
        ttk.Combobox(rf_top, textvariable=self.factor_show_var, width=5, state="readonly",
                     values=("20", "50", "100")).pack(side="left", padx=2)
        ttk.Label(rf_top, text="只 · 点击表头排序 · 双击打开详情 · 右键复制/资讯/公告",
                  foreground=FG_MUTED).pack(side="left", padx=6)
        self.factor_show_var.trace_add("write", lambda *a: self._render_factor_results())
        self.factor_buy_only_var.trace_add("write", lambda *a: self._render_factor_results())

        rcols = ("rank", "code", "name", "price", "pct", "score", "ma", "vol2",
                 "advice", "evidence", "mom", "trend", "vol", "liq",
                 "pattern", "market", "top", "industry", "asof")
        rheaders = ("排名", "代码", "名称", "现价", "涨跌幅", "因子得分", "均线", "量/前2日",
                    "次日建议", "模型证据", "动量", "趋势", "波动", "流动性",
                    "形态", "市场", "主要贡献", "行业", "数据日")
        rwidths = (44, 66, 96, 70, 68, 62, 92, 76, 84, 62, 50, 50, 50, 54,
                   50, 50, 200, 78, 78)
        self.factor_cols = rcols
        self.factor_headers = dict(zip(rcols, rheaders))
        rbox = ttk.Frame(rf)
        rbox.pack(fill="both", expand=True)
        self.factor_tree = ttk.Treeview(rbox, columns=rcols, show="headings")
        for c, h, w in zip(rcols, rheaders, rwidths):
            self.factor_tree.heading(c, text=h, command=lambda col=c: self._sort_factor_results(col))
            self.factor_tree.column(c, width=w, anchor="e")
        for c in ("code", "name", "top", "industry"):
            self.factor_tree.column(c, anchor="w")
        rysb = ttk.Scrollbar(rbox, orient="vertical", command=self.factor_tree.yview)
        rxsb = ttk.Scrollbar(rbox, orient="horizontal", command=self.factor_tree.xview)
        self.factor_tree.configure(yscrollcommand=rysb.set, xscrollcommand=rxsb.set)
        self.factor_tree.grid(row=0, column=0, sticky="nsew")
        rysb.grid(row=0, column=1, sticky="ns")
        rxsb.grid(row=1, column=0, sticky="ew")
        rbox.rowconfigure(0, weight=1)
        rbox.columnconfigure(0, weight=1)
        self.factor_tree.tag_configure("up", foreground=COLOR_UP_DEFAULT)
        self.factor_tree.tag_configure("down", foreground=COLOR_DOWN_DEFAULT)
        self.factor_tree.tag_configure("flat", foreground=COLOR_FLAT)
        self.factor_tree.tag_configure("hot", background="#123A2A")
        self.factor_tree.tag_configure("adv_strong", background="#5E4E0C")
        self.factor_tree.tag_configure("adv_buy", background="#3A2F0B")
        self.factor_tree.tag_configure("adv_caution", background="#132A3E")
        self.factor_tree.tag_configure("adv_avoid", background="#2B1C1E")
        self.factor_tree.bind("<Double-1>", self._open_factor_detail)
        self.factor_tree.bind("<Button-3>", self._on_factor_right_click)
        paned.add(rf, weight=3)
        self._factor_market_changed()

    def _sync_factor_settings(self):
        if not hasattr(self, "factor_limit_var"):
            return

        def iv(var, default):
            try:
                return int(var.get())
            except (TypeError, ValueError):
                return default

        def fv(var, default):
            try:
                return float(var.get())
            except (TypeError, ValueError):
                return default

        self.factor_limit = max(50, min(800, iv(self.factor_limit_var, self.factor_limit)))
        self.factor_lookback = max(80, min(300, iv(self.factor_lookback_var, self.factor_lookback)))
        self.factor_horizon = 5 if iv(self.factor_horizon_var, self.factor_horizon) == 5 else 1
        self.factor_threshold = max(0.0, min(100.0, fv(self.factor_threshold_var,
                                                       self.factor_threshold)))
        self.factor_exclude_st = bool(self.factor_exclude_st_var.get())
        self.factor_exclude_limit = bool(self.factor_exclude_limit_var.get())
        _ma = self.factor_ma_var.get() or "全部"
        _ma = {"上20": "站上MA20", "下20": "跌破MA20"}.get(_ma, _ma)
        _valid = ("全部", "站上MA5", "跌破MA5", "站上MA10", "跌破MA10",
                  "站上MA20", "跌破MA20", "站上MA60", "跌破MA60")
        self.factor_ma = _ma if _ma in _valid else "全部"
        _vol = self.factor_vol_var.get() or "全部"
        _vvalid = ("全部", "≈1倍(0.8~1.2)", "0.5~1.5倍",
                   "放量≥1.5倍", "放量≥2倍", "放量≥3倍", "缩量≤0.8倍")
        self.factor_vol = _vol if _vol in _vvalid else "全部"
        self.factor_market = {"个股+ETF": "all", "个股": "a", "ETF": "etf",
                              "美股": "us", "加密货币": "crypto"}.get(
            self.factor_market_var.get(), "all")
        self.factor_show_n = max(20, min(100, iv(self.factor_show_var, self.factor_show_n)))

    def _factor_ma_changed(self):
        _ma = self.factor_ma_var.get() or "全部"
        _ma = {"上20": "站上MA20", "下20": "跌破MA20"}.get(_ma, _ma)
        _valid = ("全部", "站上MA5", "跌破MA5", "站上MA10", "跌破MA10",
                  "站上MA20", "跌破MA20", "站上MA60", "跌破MA60")
        self.factor_ma = _ma if _ma in _valid else "全部"
        if self.factor_rows:
            self._render_factor_results()

    def _factor_vol_changed(self):
        self.factor_vol = self.factor_vol_var.get() or "全部"
        if self.factor_rows:
            self._render_factor_results()

    def _factor_market_changed(self):
        if not hasattr(self, "factor_market_var"):
            return
        m = {"个股+ETF": "all", "个股": "a", "ETF": "etf",
             "美股": "us", "加密货币": "crypto"}.get(
            self.factor_market_var.get(), "all")
        self.factor_market = m
        if hasattr(self, "factor_st_chk"):
            self.factor_st_chk.configure(state="normal" if m in ("a", "all") else "disabled")
        if hasattr(self, "factor_limit_chk"):
            self.factor_limit_chk.configure(
                state="normal" if m in ("a", "etf", "all") else "disabled")

    def _run_factor(self):
        if self._factor_busy:
            return
        if factor_engine is None:
            messagebox.showerror("因子引擎不可用",
                                 "未找到 factor_engine.py, 请确认它与 stock_monitor.py 同目录")
            return
        self._sync_factor_settings()
        limit = self.factor_limit
        lookback = self.factor_lookback
        horizon = self.factor_horizon
        exclude_st = self.factor_exclude_st
        exclude_limit = self.factor_exclude_limit
        market = self.factor_market
        threshold = self.factor_threshold
        self._factor_busy = True
        self._factor_cancel.clear()
        self.factor_run_btn.configure(state="disabled")
        self.factor_cancel_btn.configure(state="normal")
        self.factor_status_var.set("准备运行...")

        def progress(_stage, _done, _total, msg):
            self._factor_queue.put(("progress", msg))

        def work():
            try:
                result = factor_engine.run_factor_screen(
                    limit=limit, lookback=lookback, horizon=horizon,
                    exclude_st=exclude_st, exclude_limit_up=exclude_limit,
                    threshold=threshold, market=market,
                    workers=10 if market == "us" else 4,
                    progress_cb=progress,
                    cancel_event=self._factor_cancel)
                self._factor_queue.put(("done", result))
            except factor_engine.Cancelled:
                self._factor_queue.put(("cancelled",))
            except Exception as e:
                self._factor_queue.put(("error", str(e)))

        threading.Thread(target=work, daemon=True).start()

    def _factor_cancel_cmd(self):
        if not self._factor_busy:
            return
        self._factor_cancel.set()
        self.factor_cancel_btn.configure(state="disabled")
        self.factor_status_var.set("正在取消 (等待当前网络请求结束)...")

    def _factor_pump(self):
        try:
            while True:
                item = self._factor_queue.get_nowait()
                kind = item[0]
                if kind == "progress":
                    self.factor_status_var.set(item[1])
                elif kind == "done":
                    self._factor_done(item[1])
                elif kind == "error":
                    self._factor_error(item[1])
                elif kind == "cancelled":
                    self._factor_cancelled()
                elif kind == "industry":
                    self._factor_apply_industry(item[1])
        except queue.Empty:
            pass
        try:
            self.root.after(300, self._factor_pump)
        except Exception:
            pass

    def _factor_done(self, result):
        self.factor_rows = result.get("stocks") or []
        self.factor_stats = result.get("factor_stats") or []
        self.factor_meta = result.get("meta") or {}
        self.factor_wf = result.get("walk_forward") or {}
        self.factor_vol_stats = result.get("volume_analysis") or {}
        self.factor_sort_col = None
        self.factor_sort_desc = True
        self.factor_stat_sort_col = None
        self.factor_stat_sort_desc = True
        self._update_factor_stat_headings()
        self._update_factor_result_headings()
        self._render_factor_stats()
        self._render_factor_results()
        self._factor_busy = False
        self.factor_run_btn.configure(state="normal")
        self.factor_cancel_btn.configure(state="disabled")
        self.factor_status_var.set(self._factor_summary_text())
        self._save_config()
        self._start_factor_industry_fill()

    def _factor_error(self, msg):
        _LOG.warning("因子选股失败: %s", msg)
        self._factor_busy = False
        self.factor_run_btn.configure(state="normal")
        self.factor_cancel_btn.configure(state="disabled")
        self.factor_status_var.set(f"运行失败: {msg}")

    def _factor_cancelled(self):
        self._factor_busy = False
        self.factor_run_btn.configure(state="normal")
        self.factor_cancel_btn.configure(state="disabled")
        self.factor_status_var.set("已取消")

    def _factor_summary_text(self):
        meta = self.factor_meta or {}
        wf = self.factor_wf or {}
        oos = (wf.get("oos") or {}).get("mean_ic")
        eq = (wf.get("equal_oos") or {}).get("mean_ic")
        parts = [f"候选 {len(self.factor_rows)} 只",
                 f"入选因子 {meta.get('selected', 0)}/{len(self.factor_stats)}",
                 f"截至 {meta.get('asof') or '--'}"]
        n_strong = sum(1 for r in self.factor_rows if r.get("advice") == "强候选")
        n_buy = sum(1 for r in self.factor_rows if r.get("advice") in ("强候选", "候选"))
        n_caution = sum(1 for r in self.factor_rows if r.get("advice") == "谨慎候选")
        parts.append(f"次日买入候选 {n_buy}（强 {n_strong}，谨慎 {n_caution}）")
        if oos is not None:
            parts.append(f"样本外IC {oos:+.3f}")
        folds = [f for f in (wf.get("folds") or []) if f.get("ic") is not None]
        if folds:
            pos = sum(1 for f in folds if f["ic"] > 0)
            parts.append(f"滚动折 {pos}/{len(folds)} 正")
        if eq is not None:
            parts.append(f"等权基准 {eq:+.3f}")
        pf = wf.get("portfolio") or {}
        if pf.get("n_dates"):
            parts.append(f"Top{pf['top_k']} {pf['cum']:+.1%} vs {pf['bench_cum']:+.1%}")
            if pf.get("sharpe") is not None:
                parts.append(f"夏普 {pf['sharpe']:.2f}")
        if meta.get("elapsed") is not None:
            parts.append(f"{meta['elapsed']:.0f}s")
        text = " · ".join(parts)
        warns = list(meta.get("warnings") or [])
        if warns:
            text += " · " + "；".join(warns)
        return text

    def _show_volume_analysis(self):
        st = self.factor_vol_stats or {}
        if not st.get("n_pairs"):
            messagebox.showinfo("提示", "请先运行一次因子选股，再查看量能回测")
            return
        win = tk.Toplevel(self.root)
        win.configure(bg=BG_ROOT)
        win.title("量能回测 · 当日量/前2日量")
        win.geometry("760x620")
        win.transient(self.root)
        tf = ttk.Frame(win, padding=(8, 6))
        tf.pack(fill="both", expand=True)
        text = tk.Text(tf, wrap="word", font=("Consolas", 9),
                       background=BG_PANEL, foreground=FG_TEXT, insertbackground=FG_TEXT,
                       relief="flat", padx=10, pady=8, selectbackground=ACCENT,
                       selectforeground=BG_ROOT)
        vsb = ttk.Scrollbar(tf, orient="vertical", command=text.yview)
        text.configure(yscrollcommand=vsb.set)
        text.pack(side="left", fill="both", expand=True)
        vsb.pack(side="right", fill="y")
        text.tag_configure("h", font=("Microsoft YaHei", 11, "bold"), spacing1=10)
        text.tag_configure("buy", foreground=COLOR_UP_DEFAULT)
        text.tag_configure("muted", foreground=FG_MUTED)
        text.tag_configure("warn", foreground=ACCENT)
        lines = []
        add = lambda tag, line: lines.append((tag, line))
        add("h", "量能回测：当日成交量 / 前2日成交量")
        add("muted", f"样本：{st.get('n_dates', 0)} 个交易日 · "
                     f"{st.get('n_pairs', 0):,} 个样本对")
        base = st.get("baseline")
        hit = st.get("hit")
        add("muted", f"基准次日收益 {('--' if base is None else f'{base:+.2%}')}  ·  "
                     f"基准命中率 {('--' if hit is None else f'{hit:.1%}')}")
        add("muted", f"日度 RankIC {st.get('mean_ic') if st.get('mean_ic') is None else f'{st[chr(109)+chr(101)+chr(97)+chr(110)+chr(95)+chr(105)+chr(99)]:+.3f}'}  ·  "
                     f"ICIR {('--' if st.get('icir') is None else f'{st[chr(105)+chr(99)+chr(105)+chr(114)]:+.2f}')}  ·  "
                     f"t {('--' if st.get('t') is None else f'{st[chr(116)]:+.2f}')}")
        add("h", "分桶统计（按量/前2日倍数）")
        add("muted", f"{'区间':<12}{'样本':>10}{'平均收益':>12}{'命中率':>10}{'超额':>12}{'t':>8}")
        for b in st.get("buckets") or []:
            add("muted", f"{b['range']:<12}{b['n']:>10}{self._fmt_eval_pct(b.get('mean')):>12}"
                         f"{self._fmt_eval_hit(b.get('hit')):>10}{self._fmt_eval_pct(b.get('excess')):>12}"
                         f"{self._fmt_eval_t(b.get('t')):>8}")
        add("h", "阈值扫描（≥N倍）")
        add("muted", f"{'阈值':<10}{'样本':>10}{'平均收益':>12}{'命中率':>10}{'超额':>12}{'t':>8}")
        for b in st.get("thresholds") or []:
            add("muted", f"≥{b['threshold']:<9g}{b['n']:>10}{self._fmt_eval_pct(b.get('mean')):>12}"
                         f"{self._fmt_eval_hit(b.get('hit')):>10}{self._fmt_eval_pct(b.get('excess')):>12}"
                         f"{self._fmt_eval_t(b.get('t')):>8}")
        best = st.get("best")
        add("h", "回测结论")
        if best:
            add("buy", f"推荐关注：放量 ≥{best['threshold']:g} 倍  "
                       f"（样本 {best['n']:,}，平均 {self._fmt_eval_pct(best.get('mean'))}，"
                       f"超额 {self._fmt_eval_pct(best.get('excess'))}，t={self._fmt_eval_t(best.get('t'))}）")
        else:
            add("warn", "没有阈值同时满足样本量与正超额，暂不建议单独作为买入指标")
        add("warn", "说明：这是历史横截面统计，不是严格回测；不同市场/周期的最优倍数可能不同，"
                    "请结合因子评分、MA20 与消息面使用。")
        text.configure(state="normal")
        for tag, line in lines:
            text.insert("end", line + "\n", tag)
        text.configure(state="disabled")

    def _fmt_eval_pct(self, v):
        return "--" if v is None else f"{v:+.2%}"

    def _fmt_eval_hit(self, v):
        return "--" if v is None else f"{v:.1%}"

    def _fmt_eval_t(self, v):
        return "--" if v is None else f"{v:+.2f}"

    def _start_factor_industry_fill(self):
        rows = self.factor_rows[:50]
        if not rows:
            return

        def work():
            mapping = {}

            def one(r):
                ind = r.get("industry")
                if ind not in (None, "", "…", "—"):
                    return r.get("symbol"), ind
                try:
                    return r.get("symbol"), fetch_industry(r.get("symbol"))
                except Exception:
                    return r.get("symbol"), "—"

            with ThreadPoolExecutor(max_workers=12) as ex:
                for sym, ind in ex.map(one, rows):
                    if sym:
                        mapping[sym] = ind
            self._factor_queue.put(("industry", mapping))

        threading.Thread(target=work, daemon=True).start()

    def _factor_apply_industry(self, mapping):
        if not mapping:
            return
        for r in self.factor_rows:
            ind = mapping.get(r.get("symbol"))
            if ind:
                r["industry"] = ind
        _save_industry_cache()
        self._render_factor_results()

    def _factor_stat_sort_value(self, r, col):
        key = {"name": "label", "category": "category_label", "mean_ic": "mean_ic",
               "icir": "icir", "t": "t", "coverage": "coverage",
               "recent_ic": "recent_ic", "win_rate": "win_rate",
               "direction": "sign", "weight": "weight", "status": "status"}.get(col)
        val = r.get(key)
        if col in ("mean_ic", "icir", "t", "coverage", "recent_ic",
                   "win_rate", "direction", "weight"):
            return val
        return val or ""

    def _apply_factor_stats_sort(self):
        col = self.factor_stat_sort_col
        if not col or not self.factor_stats:
            return
        keyed = [(self._factor_stat_sort_value(r, col), r) for r in self.factor_stats]
        present = [(v, r) for v, r in keyed if v is not None]
        missing = [r for v, r in keyed if v is None]
        present.sort(key=lambda t: t[0], reverse=self.factor_stat_sort_desc)
        self.factor_stats = [r for _v, r in present] + missing

    def _update_factor_stat_headings(self):
        for c in self.factor_stat_cols:
            base = self.factor_stat_headers[c]
            if c == self.factor_stat_sort_col:
                self.fstats_tree.heading(c, text=base + (" ▼" if self.factor_stat_sort_desc else " ▲"))
            else:
                self.fstats_tree.heading(c, text=base)

    def _sort_factor_stats(self, col):
        if self.factor_stat_sort_col == col:
            self.factor_stat_sort_desc = not self.factor_stat_sort_desc
        else:
            self.factor_stat_sort_col = col
            self.factor_stat_sort_desc = True
        self._apply_factor_stats_sort()
        self._update_factor_stat_headings()
        self._render_factor_stats()

    def _render_factor_stats(self):
        self.fstats_tree.delete(*self.fstats_tree.get_children())
        for r in self.factor_stats:
            ic = r.get("mean_ic")
            icir = r.get("icir")
            t = r.get("t")
            recent = r.get("recent_ic")
            win = r.get("win_rate")
            sign = r.get("sign") or 0
            w = r.get("weight") or 0.0
            vals = (
                r.get("label") or r.get("key") or "",
                r.get("category_label") or "",
                "--" if ic is None else f"{ic:+.4f}",
                "--" if icir is None else f"{icir:+.2f}",
                "--" if t is None else f"{t:+.1f}",
                f"{(r.get('coverage') or 0) * 100:.0f}%",
                "--" if recent is None else f"{recent:+.4f}",
                "--" if win is None else f"{win * 100:.0f}%",
                "正向" if sign > 0 else ("反向" if sign < 0 else "—"),
                f"{w * 100:+.1f}%",
                r.get("status") or "",
            )
            tags = ("sel",) if w else ("off",)
            self.fstats_tree.insert("", "end", iid=r.get("key"), values=vals, tags=tags)

    def _factor_result_sort_value(self, r, col):
        if col in ("rank", "price", "pct", "score", "coverage"):
            return r.get(col)
        if col == "ma":
            return len(r.get("ma_above") or [])
        if col == "vol2":
            return r.get("vol_prev2")
        if col == "advice":
            return {"强候选": 5, "候选": 4, "谨慎候选": 3,
                    "观察": 2, "回避": 1, "数据不足": 0}.get(r.get("advice"), 0)
        if col == "evidence":
            return 1 if r.get("evidence") == "正向" else 0
        cat_key = {"mom": "momentum", "trend": "trend", "vol": "volatility",
                   "liq": "liquidity", "pattern": "pattern", "market": "market"}.get(col)
        if cat_key:
            return (r.get("cat_scores") or {}).get(cat_key)
        return r.get(col) or ""

    def _apply_factor_result_sort(self):
        col = self.factor_sort_col
        if not col or not self.factor_rows:
            return
        keyed = [(self._factor_result_sort_value(r, col), r) for r in self.factor_rows]
        present = [(v, r) for v, r in keyed if v is not None]
        missing = [r for v, r in keyed if v is None]
        present.sort(key=lambda t: t[0], reverse=self.factor_sort_desc)
        self.factor_rows = [r for _v, r in present] + missing

    def _update_factor_result_headings(self):
        for c in self.factor_cols:
            base = self.factor_headers[c]
            if c == self.factor_sort_col:
                self.factor_tree.heading(c, text=base + (" ▼" if self.factor_sort_desc else " ▲"))
            else:
                self.factor_tree.heading(c, text=base)

    def _sort_factor_results(self, col):
        if self.factor_sort_col == col:
            self.factor_sort_desc = not self.factor_sort_desc
        else:
            self.factor_sort_col = col
            self.factor_sort_desc = True
        self._apply_factor_result_sort()
        self._update_factor_result_headings()
        self._render_factor_results()

    def _eval_selected_factor(self):
        sel = self.factor_tree.selection()
        if not sel:
            messagebox.showinfo("提示", "请先在结果表中选择一只标的")
            return
        vals = self.factor_tree.item(sel[0], "values")
        if len(vals) >= 2:
            self._open_evaluation(str(vals[1]))

    def _factor_show_n(self):
        try:
            return max(20, min(100, int(self.factor_show_var.get())))
        except (TypeError, ValueError):
            return 50

    def _render_factor_results(self):
        self.factor_tree.delete(*self.factor_tree.get_children())
        if not self.factor_rows:
            return
        rows = self.factor_rows
        if self.factor_buy_only_var.get():
            rows = [r for r in rows if r.get("advice") in ("强候选", "候选")]
        vol_filter = getattr(self, "factor_vol", "全部") or "全部"
        if vol_filter != "全部":
            def vol_ok(r):
                v = r.get("vol_prev2")
                if v is None:
                    return False
                if vol_filter == "≈1倍(0.8~1.2)":
                    return 0.8 <= v <= 1.2
                if vol_filter == "0.5~1.5倍":
                    return 0.5 <= v <= 1.5
                if vol_filter.startswith("放量≥"):
                    try:
                        th = float(vol_filter.replace("放量≥", "").replace("倍", ""))
                    except ValueError:
                        return True
                    return v >= th
                if vol_filter == "缩量≤0.8倍":
                    return v <= 0.8
                return True
            rows = [r for r in rows if vol_ok(r)]
        ma_filter = getattr(self, "factor_ma", "全部") or "全部"
        if ma_filter != "全部":
            def ma_ok(r):
                dev = r.get("ma_dev") or {}
                try:
                    period = int(ma_filter.replace("站上MA", "").replace("跌破MA", ""))
                except ValueError:
                    return True
                val = dev.get(period)
                if val is None:
                    return False
                return val >= 0 if ma_filter.startswith("站上MA") else val < 0
            rows = [r for r in rows if ma_ok(r)]
        cat_keys = (("mom", "momentum"), ("trend", "trend"), ("vol", "volatility"),
                    ("liq", "liquidity"), ("pattern", "pattern"), ("market", "market"))

        def cat_text(r, key):
            v = (r.get("cat_scores") or {}).get(key)
            return "--" if v is None else f"{v:.0f}"

        adv_short = {"强候选": "★强候选", "候选": "候选", "谨慎候选": "谨慎",
                     "观察": "观察", "回避": "回避", "数据不足": "数据不足"}
        adv_tag = {"强候选": "adv_strong", "候选": "adv_buy",
                   "谨慎候选": "adv_caution", "回避": "adv_avoid",
                   "数据不足": "adv_avoid"}
        for r in rows[:self._factor_show_n()]:
            score = r.get("score")
            pct = r.get("pct")
            label = "up" if (pct or 0) > 0 else ("down" if (pct or 0) < 0 else "flat")
            advice = r.get("advice") or "观察"
            tags = ((adv_tag[advice],) if advice in adv_tag else ()) + (label,)
            _mkt = r.get("market")
            if _mkt == "crypto":
                pf = fmt_crypto_price
            elif _mkt == "etf" or is_etf(r.get("symbol") or r.get("code") or ""):
                pf = lambda v: "--" if v is None else f"{v:.3f}"
            else:
                pf = fmt_price
            vals = (
                r.get("rank") or "",
                r.get("code") or "",
                r.get("name") or "",
                pf(r.get("price")),
                fmt_pct(pct),
                "--" if score is None else f"{score:.1f}",
                r.get("ma_status") or "—",
                "--" if r.get("vol_prev2") is None else f"{r['vol_prev2']:.2f}x",
                adv_short.get(advice, advice),
                r.get("evidence") or "—",
            ) + tuple(cat_text(r, k) for _c, k in cat_keys) + (
                r.get("top") or "—",
                r.get("industry") or "—",
                r.get("asof") or "—",
            )
            self.factor_tree.insert("", "end", values=vals, tags=tags)

    def _export_factor_csv(self):
        rows = getattr(self, "factor_rows", [])
        if not rows:
            messagebox.showinfo("导出", "当前没有因子选股结果，请先运行", parent=self.root)
            return
        headers = ["排名", "代码", "名称", "市场", "现价", "涨跌幅%", "因子得分",
                   "均线", "量/前2日", "次日建议", "模型证据", "动量", "趋势",
                   "波动", "流动性", "形态", "市场分", "主要贡献", "行业", "数据日"]
        mkt_label = {"a": "A股", "etf": "ETF", "us": "美股", "crypto": "加密"}
        data = []
        for r in sorted(rows, key=lambda x: x.get("score") or -1, reverse=True):
            cat = r.get("cat_scores") or {}
            data.append([
                r.get("rank"), r.get("code"), r.get("name"),
                mkt_label.get(r.get("market"), r.get("market")),
                r.get("price"), r.get("pct"), r.get("score"),
                r.get("ma_status"), r.get("vol_prev2"),
                r.get("advice"), r.get("evidence"),
                cat.get("momentum"), cat.get("trend"), cat.get("volatility"),
                cat.get("liquidity"), cat.get("pattern"), cat.get("market"),
                r.get("top"), r.get("industry"), r.get("asof"),
            ])
        mkt = getattr(self, "factor_market", "all")
        path = export_rows_csv(
            self.root, "导出因子选股结果",
            f"factor_{mkt}_{time.strftime('%Y%m%d_%H%M')}.csv", headers, data)
        if path:
            self.factor_status_var.set(f"已导出 {len(data)} 行 → {path}")

    def _open_factor_detail(self, _event):
        sel = self.factor_tree.selection()
        if not sel:
            return
        vals = self.factor_tree.item(sel[0], "values")
        if len(vals) < 2:
            return
        c = classify_symbol(str(vals[1]))
        if c:
            webbrowser.open(detail_url(c[2], c[1]))

    def _on_factor_right_click(self, event):
        row = self.factor_tree.identify_row(event.y)
        if not row:
            return
        self.factor_tree.selection_set(row)
        vals = self.factor_tree.item(row, "values")
        if len(vals) >= 2:
            self._show_context_menu(event, str(vals[1]))

    # ================ 7x24快讯 ================
    def _build_feed_tab(self):
        ctrl = ttk.Frame(self.tab_feed, padding=(8, 6))
        ctrl.pack(fill="x")
        ttk.Button(ctrl, text="刷新", command=self._feed_refresh).pack(side="left")
        self.feed_auto_var = tk.BooleanVar(value=True)
        ttk.Checkbutton(ctrl, text="自动刷新(60秒)", variable=self.feed_auto_var).pack(side="left", padx=8)
        ttk.Label(ctrl, text="  关键词过滤:").pack(side="left")
        self.feed_kw_var = tk.StringVar()
        ent = ttk.Entry(ctrl, textvariable=self.feed_kw_var, width=18)
        ent.pack(side="left", padx=4)
        ent.bind("<KeyRelease>", lambda e: self._render_feed())
        self.feed_status_var = tk.StringVar(value="加载中...")
        ttk.Label(ctrl, textvariable=self.feed_status_var, foreground=FG_MUTED).pack(side="right")

        tf = ttk.Frame(self.tab_feed, padding=(8, 4))
        tf.pack(fill="both", expand=True)
        cols = ("time", "impact", "text", "url")
        self.ftree = ttk.Treeview(tf, columns=cols, show="headings")
        for cname, h, w, a in (("time", "时间", 96, "center"), ("impact", "影响", 56, "center"),
                               ("text", "内容", 1020, "w")):
            self.ftree.heading(cname, text=h)
            self.ftree.column(cname, width=w, anchor=a)
        self.ftree.column("url", width=0, stretch=False)
        vsb = ttk.Scrollbar(tf, orient="vertical", command=self.ftree.yview)
        self.ftree.configure(yscrollcommand=vsb.set)
        self.ftree.pack(side="left", fill="both", expand=True)
        vsb.pack(side="right", fill="y")
        self.ftree.tag_configure("利好", foreground=COLOR_UP_DEFAULT)
        self.ftree.tag_configure("利空", foreground=COLOR_DOWN_DEFAULT)
        self.ftree.tag_configure("中性", foreground=COLOR_FLAT)
        self.ftree.bind("<Double-1>", lambda e: self._open_url_from_tree(self.ftree, 3))
        self.feed_rows = []
        self._feed_queue = queue.Queue()      # 工作线程只入队, 由主线程泵渲染(不跨线程碰 Tk)
        self._feed_refresh()
        self.root.after(300, self._feed_pump)
        self.root.after(60000, self._feed_tick)

    def _feed_tick(self):
        """每 60 秒心跳: 勾选自动刷新时才真正抓取。"""
        if not self._stop:
            if self.feed_auto_var.get():
                self._feed_refresh()
            self.root.after(60000, self._feed_tick)

    def _feed_refresh(self):
        def work():
            self._feed_queue.put(fetch_flash_news(50))
        threading.Thread(target=work, daemon=True).start()

    def _feed_pump(self):
        """主线程: 排空快讯队列并渲染。"""
        try:
            while True:
                rows = self._feed_queue.get_nowait()
                self.feed_rows = rows
                self._render_feed()
                if rows:
                    self.feed_status_var.set(
                        f"新浪7x24 · 最新 {rows[0]['time']} · 共 {len(rows)} 条 · 双击打开原文")
                else:
                    self.feed_status_var.set("快讯获取失败或为空")
        except queue.Empty:
            pass
        if not self._stop:
            self.root.after(300, self._feed_pump)

    def _render_feed(self):
        self.ftree.delete(*self.ftree.get_children())
        kw = (self.feed_kw_var.get() or "").strip().lower()
        shown = 0
        for i, r in enumerate(self.feed_rows):
            if kw and kw not in r["text"].lower():
                continue
            self.ftree.insert("", "end", iid=str(i),
                              values=(r["time"], r["impact"], r["text"], r["url"]),
                              tags=(r["impact"],))
            shown += 1
        if kw:
            self.feed_status_var.set(f"过滤「{kw}」: 命中 {shown} / {len(self.feed_rows)} 条")

    # ================ 问财选股 ================
    WENCAI_PRESETS = (
        "今日涨幅4%到5%，量比大于1.5，换手率大于3%",
        "昨日涨幅1%到4%，今日涨幅4%到5%，今日涨幅大于昨日涨幅",
        "连续上涨3天，换手率大于5%，非ST，市盈率小于50",
        "近5日涨幅大于10%，总市值小于100亿，非科创板，非北交所",
    )

    def _build_wencai_tab(self):
        top = ttk.Frame(self.tab_wencai, padding=(8, 6))
        top.pack(fill="x")
        ttk.Label(top, text="自然语言:").pack(side="left")
        self.wencai_query_var = tk.StringVar(value=self.wencai_last_query)
        ent = ttk.Entry(top, textvariable=self.wencai_query_var, width=56)
        ent.pack(side="left", padx=4)
        ent.bind("<Return>", lambda e: self._wencai_run())
        self.wencai_btn = ttk.Button(top, text="查询", command=self._wencai_run)
        self.wencai_btn.pack(side="left", padx=4)
        ttk.Label(top, text="  预设:").pack(side="left")
        cb = ttk.Combobox(top, width=30, state="readonly", values=self.WENCAI_PRESETS)
        cb.pack(side="left")
        cb.bind("<<ComboboxSelected>>", lambda e: self.wencai_query_var.set(cb.get()))
        self.wencai_status_var = tk.StringVar()
        ttk.Label(top, textvariable=self.wencai_status_var, foreground=FG_MUTED).pack(side="left", padx=8)

        top2 = ttk.Frame(self.tab_wencai, padding=(8, 0))
        top2.pack(fill="x")
        ttk.Label(top2, text="Cookie:").pack(side="left")
        self.wencai_cookie_var = tk.StringVar(value=self.wencai_cookie)
        ttk.Entry(top2, textvariable=self.wencai_cookie_var, width=66).pack(side="left", padx=4)
        ttk.Label(top2, text="浏览器打开 www.iwencai.com → F12 → 控制台执行 document.cookie → 复制粘贴(本地保存)",
                  foreground=FG_MUTED).pack(side="left", padx=4)

        tf = ttk.Frame(self.tab_wencai, padding=(8, 4))
        tf.pack(fill="both", expand=True)
        self.wctree = ttk.Treeview(tf, columns=(), show="headings")
        vsb = ttk.Scrollbar(tf, orient="vertical", command=self.wctree.yview)
        self.wctree.configure(yscrollcommand=vsb.set)
        self.wctree.pack(side="left", fill="both", expand=True)
        vsb.pack(side="right", fill="y")
        self.wctree.bind("<Double-1>", self._open_wencai_detail)
        self.wctree.bind("<Button-3>", self._on_wencai_right_click)

        self.wencai_cols = []
        self.wencai_rows = []
        self._wencai_busy = False
        self._wc_sort_col = None
        self._wc_sort_desc = True
        self._wencai_queue = queue.Queue()
        ok, why = _wencai_ready()
        if ok:
            self.wencai_status_var.set("就绪 · 输入自然语言条件查询 (首次查询加载模块稍慢)")
        else:
            self.wencai_status_var.set(f"不可用: {why}")
            self.wencai_btn.configure(state="disabled")
        self.root.after(300, self._wencai_pump)

    def _wencai_run(self):
        if self._wencai_busy:
            return
        query = (self.wencai_query_var.get() or "").strip()
        if not query:
            messagebox.showinfo("提示", "请输入自然语言条件, 如: 今日涨幅大于4%，量比大于1.5")
            return
        self.wencai_cookie = (self.wencai_cookie_var.get() or "").strip()
        self.wencai_last_query = query
        self._save_config()
        self._wencai_busy = True
        self.wencai_btn.configure(state="disabled")
        self.wencai_status_var.set("查询中... (首次加载模块较慢, 请稍候)")

        def work():
            try:
                cols, rows = wencai_query(query, self.wencai_cookie)
                self._wencai_queue.put({"ok": True, "cols": cols, "rows": rows})
            except Exception as e:
                self._wencai_queue.put({"ok": False, "err": str(e)})
        threading.Thread(target=work, daemon=True).start()

    def _wencai_pump(self):
        """主线程: 排空问财查询结果并渲染(工作线程只入队)。"""
        try:
            while True:
                res = self._wencai_queue.get_nowait()
                self._wencai_busy = False
                self.wencai_btn.configure(state="normal")
                if res.get("ok"):
                    self._render_wencai(res["cols"], res["rows"])
                else:
                    self.wencai_status_var.set(res.get("err", "查询失败"))
        except queue.Empty:
            pass
        if not self._stop:
            self.root.after(300, self._wencai_pump)

    def _render_wencai(self, cols, rows):
        rows = rows[:300]
        shown = cols[:12]
        self.wencai_cols, self.wencai_rows = cols, rows
        self.wctree.delete(*self.wctree.get_children())
        self.wctree.configure(columns=shown)
        for i, c in enumerate(shown):
            w = 84 if c == "股票代码" else (120 if c == "股票简称" else 100)
            self.wctree.heading(c, text=c, command=lambda col=c: self._sort_wencai(col))
            self.wctree.column(c, width=w, anchor="w" if i < 2 else "e")
        self._wencai_fill()
        cap = " · 仅显示前300条" if len(rows) >= 300 else ""
        extra = f" · 仅显示前12列(共{len(cols)}列)" if len(cols) > 12 else ""
        self.wencai_status_var.set(
            f"共 {len(rows)} 条{cap}{extra} · 表头排序 · 右键复制/查资讯 · 双击详情")

    def _wencai_fill(self):
        self.wctree.delete(*self.wctree.get_children())
        n = min(12, len(self.wencai_cols))
        for r in self.wencai_rows:
            vals = [_wc_disp(v) for v in r[:n]]
            while len(vals) < n:
                vals.append("")
            self.wctree.insert("", "end", values=vals)

    def _sort_wencai(self, col):
        if col not in self.wencai_cols:
            return
        if self._wc_sort_col == col:
            self._wc_sort_desc = not self._wc_sort_desc
        else:
            self._wc_sort_col = col
            self._wc_sort_desc = True
        i = self.wencai_cols.index(col)

        def kord(r):
            v = r[i] if i < len(r) else ""
            f = _wc_num(v)
            if f is not None:
                return (0, f)
            return (1, str(v))
        self.wencai_rows.sort(key=kord, reverse=self._wc_sort_desc)
        self._wencai_fill()

    def _wencai_selected_code(self, item):
        vals = self.wctree.item(item, "values")
        if not self.wencai_cols or "股票代码" not in self.wencai_cols[:12]:
            return ""
        return _wc_code_of(vals[self.wencai_cols.index("股票代码")])

    def _on_wencai_right_click(self, event):
        row = self.wctree.identify_row(event.y)
        if not row:
            return
        self.wctree.selection_set(row)
        code = self._wencai_selected_code(row)
        if code:
            self._show_context_menu(event, code)

    def _open_wencai_detail(self, _event):
        sel = self.wctree.selection()
        if not sel:
            return
        code = self._wencai_selected_code(sel[0])
        c = classify_symbol(code) if code else None
        if c:
            _t, disp, mkt = c
            webbrowser.open(detail_url(mkt, disp))

    def _screen_to_wencai(self):
        if getattr(self, "screen_market", "a") != "a":
            messagebox.showinfo("提示", "问财选股仅支持 A股；美股/ETF 请直接用本地筛选")
            return
        """把选股器当前条件翻译成问财自然语言查询, 并跳转到问财页。"""
        def f(var):
            try:
                return float(var.get())
            except (TypeError, ValueError):
                return None
        parts = []
        f_min, f_max = f(self.f_min_var), f(self.f_max_var)
        if f_min is not None and f_max is not None:
            parts.append(f"今日涨幅{min(f_min, f_max):g}%到{max(f_min, f_max):g}%")
        lb, hs = f(self.f_lb_var), f(self.f_hs_var)
        if lb is not None:
            parts.append(f"量比大于{lb:g}")
        if hs is not None:
            parts.append(f"换手率大于{hs:g}%")
        p_min, p_max = f(self.f_prev_min_var), f(self.f_prev_max_var)
        if p_min is not None and p_max is not None:
            parts.append(f"昨日涨幅{min(p_min, p_max):g}%到{max(p_min, p_max):g}%")
        elif p_min is not None:
            parts.append(f"昨日涨幅大于{p_min:g}%")
        elif p_max is not None:
            parts.append(f"昨日涨幅小于{p_max:g}%")
        st = f(self.f_streak_var)
        if st is not None:
            parts.append(f"连续上涨{int(st)}天")
        if self.f_accel_var.get():
            parts.append("今日涨幅大于昨日涨幅")
        if not parts:
            messagebox.showinfo("提示", "请先填写至少一个选股条件")
            return
        self.wencai_query_var.set("，".join(parts))
        self.nb.select(self.tab_wencai)
        self.wencai_status_var.set("已从选股器生成条件, 点「查询」执行 (需有效 cookie)")

    # ---------------- 关闭 ----------------
    def _on_close(self):
        self._stop = True
        self._factor_cancel.set()
        self._sync_factor_settings()
        self._save_config()
        _save_industry_cache()
        _save_kline_cache()
        self.root.destroy()


def main():
    _load_industry_cache()
    _load_kline_cache()
    root = tk.Tk()
    app = StockMonitorApp(root)
    app._poll()
    root.mainloop()


if __name__ == "__main__":
    main()
