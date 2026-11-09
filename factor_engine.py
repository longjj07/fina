#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
零依赖多因子选股引擎 (Python 标准库)。

定位:
  幻方量化官网没有公开因子定义; 本模块采用其公开的方法论框架
  (全市场、数据驱动、横截面排序、AI/统计建模), 具体因子均为通用的公开量价因子,
  不代表幻方量化的专有因子, 也不构成任何投资建议。

流程:
  1) 取今日成交额前 N 的 A 股作为研究股票池;
  2) 抓取日K, 计算 40+ 个量价/流动性/形态/市场因子;
  3) 以「次日开盘买入、持有 h 日收盘卖出」为前瞻收益, 计算逐日横截面 RankIC;
  4) 按 ICIR、覆盖率、t 值、方向一致性筛选因子, 并剔除高相关因子;
  5) 前 70% 日期训练权重, 后 30% 日期做样本外检验;
  6) 用全样本权重给当前截面打分 (0~100), 输出明细与因子贡献。

用法:
  python factor_engine.py --selftest                 # 离线自检
  python factor_engine.py --limit 30 --lookback 120  # 联网小样本试跑
  python factor_engine.py --limit 300                # 全量研究
"""

import argparse
import datetime
import json
import math
import os
import random
import socket
import sys
import threading
import time
import urllib.request
import urllib.parse
from array import array
from collections import deque
from concurrent.futures import ThreadPoolExecutor, as_completed

UA = {"User-Agent": "Mozilla/5.0 (Windows NT 10.0; Win64; x64)"}
SINA_HDR = {"User-Agent": UA["User-Agent"], "Referer": "https://finance.sina.com.cn/"}
SINA_LIST_URL = ("https://vip.stock.finance.sina.com.cn/quotes_service/api/json_v2.php/"
                 "Market_Center.getHQNodeData?page={page}&num={num}&sort=amount&asc=0"
                 "&node={node}&symbol=")
KLINE_URL = "https://web.ifzq.gtimg.cn/appstock/app/fqkline/get?param={sym},day,,,{n},qfq"
BINANCE_ALL_URL = "https://api.binance.com/api/v3/ticker/24hr"
BINANCE_KLINES_URL = ("https://api.binance.com/api/v3/klines?"
                      "symbol={sym}&interval=1d&limit={n}")
OKX_CANDLES_URL = "https://www.okx.com/api/v5/market/candles?instId={inst}&bar=1D&limit={n}"
NASDAQ_SCREENER_URL = ("https://api.nasdaq.com/api/screener/stocks?"
                       "tableonly=true&limit=25&offset=0&download=true")
# Yahoo 接口地址保留为可配置: 设置环境变量 FINA_YAHOO_BASE 可换成镜像/代理地址
YAHOO_BASE = os.environ.get("FINA_YAHOO_BASE",
                            "https://query1.finance.yahoo.com").rstrip("/")
# 美股数据源优先级: yahoo=Yahoo(默认) / em=东方财富(直连)
US_SOURCE = os.environ.get("FINA_US_SOURCE", "yahoo").strip().lower()
YAHOO_SCREENER_FIELDS = ",".join((
    "symbol", "longName", "shortName", "quoteType", "sector", "industry",
    "regularMarketPrice", "regularMarketChangePercent", "regularMarketChange",
    "regularMarketVolume", "regularMarketOpen", "regularMarketDayHigh",
    "regularMarketDayLow", "regularMarketPreviousClose", "regularMarketTime",
    "marketCap", "trailingPE", "priceToBook", "sharesOutstanding",
    "averageDailyVolume10Day", "fullExchangeName",
))
YAHOO_SCREENER_URL = (YAHOO_BASE + "/v1/finance/screener/predefined/saved"
                      "?scrIds=most_actives&count={count}&start={start}&fields="
                      + YAHOO_SCREENER_FIELDS)
NASDAQ_HIST_URL = ("https://api.nasdaq.com/api/quote/{sym}/historical?"
                   "assetclass=stocks&fromdate={fromdate}&limit={n}")
YAHOO_DAILY_URL = (YAHOO_BASE + "/v8/finance/chart/"
                   "{sym}?interval=1d&range={rng}")
# 东方财富美股(国内直连): 列表 / 日K / 指数
EM_US_LIST_URL = ("https://push2.eastmoney.com/api/qt/clist/get?"
                  "pn={page}&pz=100&po=1&np=1&fltt=2&invt=2&fid=f6"
                  "&fs=m:105,m:106,m:107"
                  "&fields=f2,f3,f5,f6,f8,f9,f10,f12,f13,f14,f15,f16,f17,"
                  "f18,f20,f23,f100")
EM_KLINE_URL = ("https://push2his.eastmoney.com/api/qt/stock/kline/get?"
                "secid={secid}&klt=101&fqt=1&lmt={n}&end=20500101"
                "&fields1=f1,f2,f3,f4,f5,f6&fields2=f51,f52,f53,f54,f55,f56")
EM_US_INDEX_SECIDS = ("100.SPX", "100.DJIA", "100.NDX")
US_FALLBACK = [
    "AAPL", "MSFT", "NVDA", "GOOGL", "AMZN", "META", "TSLA", "AVGO", "AMD",
    "NFLX", "JPM", "V", "MA", "COST", "HD", "UNH", "XOM", "JNJ", "WMT", "PG",
    "LLY", "ORCL", "CRM", "ADBE", "CSCO", "INTC", "QCOM", "TXN", "MU", "AMAT",
    "BAC", "WFC", "GS", "MS", "C", "BLK", "SPGI", "CAT", "DE", "GE",
]
CRYPTO_STABLE = {
    "USDC", "FDUSD", "TUSD", "DAI", "USDP", "BUSD", "EUR", "AEUR", "USDD",
    "PYUSD", "USD1", "XAUT", "PAXG", "RLUSD",
}
KLINE_HDR = {"User-Agent": UA["User-Agent"], "Referer": "https://gu.qq.com/"}
SINA_KLINE_URL = ("https://money.finance.sina.com.cn/quotes_service/api/json_v2.php/"
                  "CN_MarketData.getKLineData?symbol={sym}&scale=240&ma=no&datalen={n}")
INDEX_SYMBOL = "sh000300"
CACHE_FILE = os.path.join(os.path.dirname(os.path.abspath(__file__)), "factor_cache.json")
CACHE_VERSION = 1
CACHE_TTL = 1800.0
MISS_TTL = 600.0
TRADING_DAYS = 252
NAN = float("nan")


class Cancelled(Exception):
    pass


# 类别 key -> 中文名
CATEGORIES = (
    ("momentum", "动量"),
    ("trend", "趋势"),
    ("volatility", "波动"),
    ("liquidity", "流动性"),
    ("pattern", "形态"),
    ("market", "市场"),
)
CATEGORY_LABEL = dict(CATEGORIES)

# key -> (显示名, 类别 key, 定义)
FACTOR_DEFS = {
    "ret_1": ("1日收益", "momentum", "C_t/C_{t-1}-1"),
    "ret_5": ("5日收益", "momentum", "C_t/C_{t-5}-1"),
    "ret_10": ("10日收益", "momentum", "C_t/C_{t-10}-1"),
    "ret_20": ("20日收益", "momentum", "C_t/C_{t-20}-1"),
    "ret_60": ("60日收益", "momentum", "C_t/C_{t-60}-1"),
    "mom_5_1": ("5日动量(剔除1日)", "momentum", "C_{t-1}/C_{t-6}-1"),
    "mom_10_1": ("10日动量(剔除1日)", "momentum", "C_{t-1}/C_{t-11}-1"),
    "mom_20_1": ("20日动量(剔除1日)", "momentum", "C_{t-1}/C_{t-21}-1"),
    "ma_dev_5": ("偏离MA5", "trend", "C_t/MA5-1"),
    "ma_dev_10": ("偏离MA10", "trend", "C_t/MA10-1"),
    "ma_dev_20": ("偏离MA20", "trend", "C_t/MA20-1"),
    "ma_dev_60": ("偏离MA60", "trend", "C_t/MA60-1"),
    "slope_20": ("20日趋势斜率", "trend", "log(close) 对时间 OLS 斜率"),
    "rsi_14": ("RSI14", "trend", "(RSI-50)/50"),
    "macd_hist": ("MACD柱", "trend", "(DIF-DEA)/close"),
    "max_ret_20": ("20日最大单日涨幅", "momentum", "max(日收益, 20日)"),
    "realvol_5": ("5日已实现波动", "volatility", "std(log收益,5)*sqrt(252)"),
    "realvol_20": ("20日已实现波动", "volatility", "std(log收益,20)*sqrt(252)"),
    "realvol_60": ("60日已实现波动", "volatility", "std(log收益,60)*sqrt(252)"),
    "downvol_20": ("20日下行波动", "volatility", "sqrt(mean(min(r,0)^2))*sqrt(252)"),
    "atr_14": ("ATR14/价格", "volatility", "ATR14/close"),
    "mdd_60": ("60日最大回撤", "volatility", "min(C/cummax-1)"),
    "range_20": ("20日振幅", "volatility", "(max(high)-min(low))/close"),
    "skew_20": ("20日收益偏度", "volatility", "日收益三阶矩"),
    "kurt_20": ("20日收益峰度", "volatility", "日收益四阶矩"),
    "autocorr_20": ("收益自相关", "volatility", "lag1 自相关(20日)"),
    "volratio_5": ("5日/20日量比", "liquidity", "mean(V,5)/mean(V,20)"),
    "vol_trend_20": ("20日量能趋势", "liquidity", "log(volume) 对时间 OLS 斜率"),
    "vol_cv_20": ("20日量能变异", "liquidity", "std(V,20)/mean(V,20)"),
    "amihud_20": ("Amihud非流动性", "liquidity", "mean(|r|/(close*volume))"),
    "pv_corr_20": ("量价相关性", "liquidity", "corr(收益, log量变化)"),
    "obv_slope_20": ("OBV斜率", "liquidity", "20日OBV变化/平均量"),
    "mfi_14": ("MFI14", "liquidity", "(MFI-50)/50"),
    "close_pos_5": ("5日收盘位置", "pattern", "mean((C-L)/(H-L))"),
    "close_pos_20": ("20日收盘位置", "pattern", "mean((C-L)/(H-L))"),
    "upper_shadow_20": ("20日上影线", "pattern", "mean((H-max(O,C))/C)"),
    "lower_shadow_20": ("20日下影线", "pattern", "mean((min(O,C)-L)/C)"),
    "pos_day_ratio_20": ("20日上涨天数占比", "pattern", "mean(ret>0)"),
    "gap_20": ("20日跳空幅度", "pattern", "mean((O_t-C_{t-1})/C_{t-1})"),
    "beta_60": ("60日Beta", "market", "cov(r, index)/var(index)"),
    "corr_60": ("60日指数相关", "market", "corr(r, index)"),
    "resid_mom_20": ("20日残差动量", "market", "ret20 - beta*index_ret20"),
}
FACTOR_KEYS = tuple(FACTOR_DEFS)


# ---------------------------------------------------------------------------
# 基础工具
# ---------------------------------------------------------------------------

_PROXY_CHECK = {"ts": 0.0, "alive": None}
_DIRECT_OPENER = None


def _proxy_usable():
    """系统代理存在但进程未运行时返回 False, 改用直连。"""
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
                   "gtimg.cn", "qq.com")


def _is_domestic(url):
    host = (urllib.parse.urlsplit(url).hostname or "").lower()
    return any(host == h or host.endswith("." + h) for h in _DOMESTIC_HOSTS)


def _http(url, headers, timeout=10):
    global _DIRECT_OPENER
    req = urllib.request.Request(url, headers=headers)
    if _is_domestic(url) or not _proxy_usable():
        if _DIRECT_OPENER is None:
            _DIRECT_OPENER = urllib.request.build_opener(urllib.request.ProxyHandler({}))
        with _DIRECT_OPENER.open(req, timeout=timeout) as resp:
            return resp.read()
    with urllib.request.urlopen(req, timeout=timeout) as resp:
        return resp.read()


def _to_float(x, default=None):
    try:
        v = float(x)
        return v if math.isfinite(v) else default
    except (TypeError, ValueError):
        return default


def _mean(xs):
    vals = [x for x in xs if x is not None and math.isfinite(x)]
    return sum(vals) / len(vals) if vals else None


def _std(xs, ddof=1):
    vals = [x for x in xs if x is not None and math.isfinite(x)]
    n = len(vals)
    if n <= ddof:
        return None
    m = sum(vals) / n
    return math.sqrt(sum((x - m) ** 2 for x in vals) / (n - ddof))


def _pearson(xs, ys):
    if len(xs) != len(ys):
        n = min(len(xs), len(ys))
        xs, ys = xs[:n], ys[:n]
    pairs = [(x, y) for x, y in zip(xs, ys)
             if x is not None and y is not None and math.isfinite(x) and math.isfinite(y)]
    n = len(pairs)
    if n < 5:
        return None
    mx = sum(x for x, _ in pairs) / n
    my = sum(y for _, y in pairs) / n
    sxx = sum((x - mx) ** 2 for x, _ in pairs)
    syy = sum((y - my) ** 2 for _, y in pairs)
    if sxx <= 0 or syy <= 0:
        return None
    sxy = sum((x - mx) * (y - my) for x, y in pairs)
    return sxy / math.sqrt(sxx * syy)


def _mdd(closes):
    peak = -float("inf")
    worst = 0.0
    for c in closes:
        if c is None or c <= 0:
            continue
        peak = max(peak, c)
        if peak > 0:
            worst = min(worst, c / peak - 1.0)
    return worst if peak > -float("inf") else None


def _rankdata(vals):
    pairs = [(i, v) for i, v in enumerate(vals) if v is not None and math.isfinite(v)]
    out = [None] * len(vals)
    m = len(pairs)
    if not m:
        return out
    pairs.sort(key=lambda t: t[1])
    j = 0
    while j < m:
        k = j
        while k < m and pairs[k][1] == pairs[j][1]:
            k += 1
        avg = (j + k - 1) / 2.0
        for idx, _ in pairs[j:k]:
            out[idx] = avg
        j = k
    return out


def _percentile_rank(vals):
    ranks = _rankdata(vals)
    m = sum(1 for r in ranks if r is not None)
    if m <= 1:
        return [0.5 if r is not None else None for r in ranks]
    return [r / (m - 1.0) if r is not None else None for r in ranks]


def _spearman(xs, ys):
    pairs = [(x, y) for x, y in zip(xs, ys)
             if x is not None and y is not None and math.isfinite(x) and math.isfinite(y)]
    if len(pairs) < 10:
        return None
    rx = _rankdata([x for x, _ in pairs])
    ry = _rankdata([y for _, y in pairs])
    return _pearson(rx, ry)


def _rank_ic_at(arr, fwd, off, S, min_names):
    """两个已排名数组的 Pearson 相关(=Spearman IC); 返回 (ic, pairs)。"""
    n = 0
    sx = sy = sxx = syy = sxy = 0.0
    for si in range(S):
        x = arr[off + si]
        y = fwd[si]
        if math.isfinite(x) and math.isfinite(y):
            n += 1
            sx += x
            sy += y
            sxx += x * x
            syy += y * y
            sxy += x * y
    if n < min_names:
        return None, n
    cov = sxy - sx * sy / n
    vx = sxx - sx * sx / n
    vy = syy - sy * sy / n
    if vx <= 0 or vy <= 0:
        return None, n
    return cov / math.sqrt(vx * vy), n


def _bj_now():
    t = time.gmtime(time.time() + 8 * 3600)
    return time.strftime("%Y-%m-%d", t), t.tm_hour * 60 + t.tm_min


def _check(cancel_event):
    if cancel_event is not None and cancel_event.is_set():
        raise Cancelled()


def _emit(progress_cb, stage, done, total, msg):
    if progress_cb is None:
        return
    try:
        progress_cb(stage, done, total, msg)
    except Exception:
        pass


# ---------------------------------------------------------------------------
# 数据抓取与缓存
# ---------------------------------------------------------------------------

def fetch_sina_universe(limit=300, exclude_st=True, node="hs_a", market="a"):
    """成交额降序的 A 股/ETF 池。"""
    out = []
    seen = set()
    page = 1
    max_page = max(2, int(limit / 100) + 3)
    while len(out) < limit and page <= max_page:
        url = SINA_LIST_URL.format(page=page, num=100, node=node)
        try:
            raw = _http(url, SINA_HDR, timeout=12)
            arr = json.loads(raw.decode("utf-8", "replace"))
        except Exception:
            break
        if not arr:
            break
        for r in arr:
            sym = str(r.get("symbol") or "")
            if not sym.startswith(("sh", "sz", "bj")) or sym in seen:
                continue
            name = str(r.get("name") or "")
            if exclude_st and ("ST" in name.upper() or "退" in name):
                continue
            if node == "etf_hq_fund" and any(
                    k in name for k in ("货币", "日利", "短融", "现金", "债", "添益",
                                       "理财", "保证金", "快线", "国开", "政金")):
                continue
            price = _to_float(r.get("trade"))
            amount = _to_float(r.get("amount"))
            if price is None or price <= 0 or amount is None or amount <= 0:
                continue
            seen.add(sym)
            out.append({
                "symbol": sym,
                "code": str(r.get("code") or sym[2:]),
                "name": name,
                "price": price,
                "pct": _to_float(r.get("changepercent")),
                "amount": amount,
                "turnover": _to_float(r.get("turnoverratio")),
                "high": _to_float(r.get("high")),
                "low": _to_float(r.get("low")),
                "open": _to_float(r.get("open")),
                "volume": _to_float(r.get("volume")),
                "market": market,
            })
            if len(out) >= limit:
                break
        page += 1
    return out


def _parse_bars(arr, today_str, before_close):
    out = []
    for b in arr:
        if not isinstance(b, (list, tuple)) or len(b) < 6:
            continue
        date = str(b[0])[:10]
        try:
            o, c, h, l, v = (float(b[1]), float(b[2]), float(b[3]),
                             float(b[4]), float(b[5]))
        except (TypeError, ValueError):
            continue
        if not all(math.isfinite(x) for x in (o, c, h, l, v)):
            continue
        if c <= 0 or h < l or v < 0:
            continue
        out.append((date, o, c, h, l, v))
    ded = {}
    for row in out:
        if row[0] <= today_str:
            ded[row[0]] = row
    rows = sorted(ded.values(), key=lambda x: x[0])
    # 当日盘中未定型 bar 不参与因子/训练
    if rows and rows[-1][0] == today_str and before_close:
        rows = rows[:-1]
    return rows


def _fetch_tencent_bars(symbol, n):
    try:
        raw = _http(KLINE_URL.format(sym=symbol, n=n), KLINE_HDR, timeout=10)
        data = json.loads(raw.decode("utf-8", "replace"))
        node = (data.get("data") or {}).get(symbol) or {}
        arr = node.get("qfqday") or node.get("day") or []
        today, minutes = _bj_now()
        return _parse_bars(arr, today, minutes < 15 * 60 + 10)
    except Exception:
        return []


def _fetch_sina_bars(symbol, n):
    """腾讯限流时的回退源。新浪日K为不复权价, 成交量按股/100 统一成手。"""
    try:
        raw = _http(SINA_KLINE_URL.format(sym=symbol, n=n), SINA_HDR, timeout=10)
        arr = json.loads(raw.decode("utf-8", "replace"))
        if not isinstance(arr, list):
            return []
        rows = []
        for x in arr:
            if not isinstance(x, dict):
                continue
            o = _to_float(x.get("open"))
            c = _to_float(x.get("close"))
            h = _to_float(x.get("high"))
            l = _to_float(x.get("low"))
            v = _to_float(x.get("volume"))
            date = str(x.get("day") or "")[:10]
            if None in (o, c, h, l, v) or not date:
                continue
            rows.append((date, o, c, h, l, v / 100.0))
        today, minutes = _bj_now()
        return _parse_bars(rows, today, minutes < 15 * 60 + 10)
    except Exception:
        return []


def _fetch_bars_with_source(symbol, n, prefer_tencent=True, throttle=True):
    if prefer_tencent:
        if throttle:
            time.sleep(0.02 + random.random() * 0.04)
        bars = _fetch_tencent_bars(symbol, n)
        if bars:
            return bars, "tencent", True
    if throttle:
        time.sleep(0.02 + random.random() * 0.04)
    bars = _fetch_sina_bars(symbol, n)
    if bars:
        return bars, "sina", False
    return [], "", False


def fetch_daily_bars(symbol, n=320):
    bars, _source, _ok = _fetch_bars_with_source(
        symbol, n, prefer_tencent=True, throttle=False)
    return bars


def fetch_crypto_universe(limit=120):
    """Binance USDT 现货按 24h 成交额排序, 过滤稳定币/杠杆代币。"""
    raw = _http(BINANCE_ALL_URL, UA, timeout=20)
    arr = json.loads(raw.decode("utf-8", "replace"))
    rows = []
    for x in arr if isinstance(arr, list) else []:
        pair = str(x.get("symbol") or "")
        if not pair.endswith("USDT"):
            continue
        base = pair[:-4]
        if base in CRYPTO_STABLE:
            continue
        lev = False
        for suf in ("UP", "DOWN", "BULL", "BEAR", "3L", "3S"):
            if base.endswith(suf) and len(base) - len(suf) >= 2:
                lev = True
                break
        if lev:
            continue
        qv = _to_float(x.get("quoteVolume"), 0)
        price = _to_float(x.get("lastPrice"))
        if not qv or price is None or qv < 5e6:
            continue
        rows.append({
            "symbol": "cr" + pair, "code": base, "name": base,
            "price": price, "pct": _to_float(x.get("priceChangePercent")),
            "amount": qv, "turnover": None, "market": "crypto",
        })
    rows.sort(key=lambda r: r["amount"], reverse=True)
    return rows[:limit]


def _fetch_crypto_bars_src(pair, n=320):
    today = time.strftime("%Y-%m-%d", time.gmtime())
    try:
        raw = _http(BINANCE_KLINES_URL.format(sym=pair, n=n), UA, timeout=10)
        arr = json.loads(raw.decode("utf-8", "replace"))
        rows = []
        for k in arr if isinstance(arr, list) else []:
            if not isinstance(k, (list, tuple)) or len(k) < 6:
                continue
            date = time.strftime("%Y-%m-%d", time.gmtime(float(k[0]) / 1000.0))
            o, c, h, l, v = (_to_float(k[1]), _to_float(k[4]), _to_float(k[2]),
                             _to_float(k[3]), _to_float(k[5], 0))
            if None in (o, c, h, l) or c <= 0:
                continue
            rows.append((date, o, c, h, l, v))
        rows = [r for r in rows if r[0] <= today]
        if rows and rows[-1][0] == today:
            rows = rows[:-1]
        if rows:
            return rows, "binance"
    except Exception:
        pass
    try:
        inst = pair[:-4] + "-USDT" if pair.endswith("USDT") else pair
        raw = _http(OKX_CANDLES_URL.format(inst=inst, n=n), UA, timeout=10)
        data = json.loads(raw.decode("utf-8", "replace"))
        rows = []
        for k in (data.get("data") or []):
            if len(k) < 6:
                continue
            date = time.strftime("%Y-%m-%d", time.gmtime(float(k[0]) / 1000.0))
            o, c, h, l, v = (_to_float(k[1]), _to_float(k[4]), _to_float(k[2]),
                             _to_float(k[3]), _to_float(k[5], 0))
            if None in (o, c, h, l) or c <= 0:
                continue
            rows.append((date, o, c, h, l, v))
        rows.sort(key=lambda r: r[0])
        rows = [r for r in rows if r[0] <= today]
        if rows and rows[-1][0] == today:
            rows = rows[:-1]
        return rows, "okx"
    except Exception:
        return [], ""


def fetch_crypto_bars(pair, n=320):
    return _fetch_crypto_bars_src(pair, n)[0]


def _us_money(v):
    x = str(v or "").replace("$", "").replace(",", "").replace("%", "").strip()
    if x in ("", "N/A", "--", "-"):
        return None
    try:
        return float(x)
    except (TypeError, ValueError):
        return None


# 海外源熔断: Yahoo/Nasdaq 连续失败后暂停 10 分钟, 避免每次运行都等超时
_SRC_LOCK = threading.Lock()
_SRC_STATE = {"yahoo": [0, 0.0], "nasdaq": [0, 0.0]}
_SRC_TTL = 600.0


def _src_ok(name):
    with _SRC_LOCK:
        return time.time() >= _SRC_STATE[name][1]


def _src_mark(name, ok):
    with _SRC_LOCK:
        fails, off = _SRC_STATE[name]
        if ok:
            _SRC_STATE[name] = [0, 0.0]
        else:
            fails += 1
            _SRC_STATE[name] = [fails, time.time() + _SRC_TTL if fails >= 2 else off]


_YAHOO_PROBE = {"ts": 0.0, "ok": None}


def _yahoo_probe():
    """探测 Yahoo 是否真的可用(代理开/关都适用); 两次失败才熔断 10 分钟。"""
    now = time.time()
    if _YAHOO_PROBE["ok"] is not None and now - _YAHOO_PROBE["ts"] < _SRC_TTL:
        return _YAHOO_PROBE["ok"]
    ok = False
    for _ in range(2):
        try:
            _http(YAHOO_BASE + "/v8/finance/chart/SPY?interval=1d&range=1d",
                  UA, timeout=4)
            ok = True
            break
        except Exception:
            ok = False
    _YAHOO_PROBE.update(ts=now, ok=ok)
    with _SRC_LOCK:
        _SRC_STATE["yahoo"] = [0, 0.0] if ok else [2, now + _SRC_TTL]
    return ok


# 美股 code -> 东财市场号(105=纳斯达克,106=纽交所,107=美交所)
_EM_US_MARKET = {}


def _fetch_us_universe_em(limit=150):
    """东方财富美股列表(国内直连), 含价格/涨跌幅/成交额/市值/PE/PB/行业。"""
    out = []
    seen = set()
    page = 1
    max_page = max(2, limit // 100 + 3)
    while len(out) < limit and page <= max_page:
        try:
            raw = _http(EM_US_LIST_URL.format(page=page), UA, timeout=12)
            data = json.loads(raw.decode("utf-8", "replace"))
        except Exception:
            break
        rows = (data.get("data") or {}).get("diff") or []
        if not rows:
            break
        for r in rows:
            raw_code = str(r.get("f12") or "").strip().upper()
            price = _to_float(r.get("f2"))
            vol = _to_float(r.get("f5"), 0) or 0
            if not raw_code or price is None or price <= 0 or vol <= 0:
                continue
            code = raw_code.replace("_", ".")
            if code in seen:
                continue
            seen.add(code)
            mkt = int(r.get("f13") or 0) or None
            if mkt:
                _EM_US_MARKET[code] = mkt
            amount = _to_float(r.get("f6"))
            out.append({
                "symbol": "us" + code, "code": code,
                "em_code": raw_code,
                "em_secid": f"{mkt}.{raw_code}" if mkt else None,
                "name": str(r.get("f14") or code),
                "price": price,
                "pct": _to_float(r.get("f3")),
                "amount": amount if amount is not None else vol * price,
                "volume": vol,
                "high": _to_float(r.get("f15")),
                "low": _to_float(r.get("f16")),
                "open": _to_float(r.get("f17")),
                "prev_close": _to_float(r.get("f18")),
                "market_cap": _to_float(r.get("f20"), 0) or 0,
                "pe": _to_float(r.get("f9")),
                "pb": _to_float(r.get("f23")),
                "lb": _to_float(r.get("f10")),
                "hs": _to_float(r.get("f8")),
                "industry": r.get("f100") if r.get("f100") not in (None, "-") else None,
                "turnover": None, "market": "us",
            })
        if len(rows) < 100:
            break
        page += 1
    out.sort(key=lambda x: x["amount"], reverse=True)
    return out[:limit]


def _fetch_em_us_bars(code, n=320, market_id=None, em_code=None):
    """东方财富美股日K(前复权), 代码 BRK.B -> BRK_B。"""
    raw_code = em_code or str(code).replace(".", "_").upper()
    ids = []
    if market_id:
        ids.append(int(market_id))
    for m in (105, 106, 107):
        if m not in ids:
            ids.append(m)
    for m in ids:
        try:
            raw = _http(EM_KLINE_URL.format(secid=f"{m}.{raw_code}",
                                            n=max(10, int(n))), UA, timeout=12)
            data = json.loads(raw.decode("utf-8", "replace")).get("data") or {}
            rows = []
            for line in data.get("klines") or []:
                p = str(line).split(",")
                if len(p) < 6:
                    continue
                try:
                    date = p[0][:10]
                    o, c, h, l, v = (float(p[1]), float(p[2]), float(p[3]),
                                     float(p[4]), float(p[5]))
                except (TypeError, ValueError):
                    continue
                if c <= 0:
                    continue
                rows.append((date, o, c, h, l, v))
            if rows:
                _EM_US_MARKET[code] = m
                return rows[-n:]
        except Exception:
            continue
    return []


def _fetch_em_index_bars(n=320):
    for secid in EM_US_INDEX_SECIDS:
        try:
            raw = _http(EM_KLINE_URL.format(secid=secid, n=max(10, int(n))),
                        UA, timeout=12)
            data = json.loads(raw.decode("utf-8", "replace")).get("data") or {}
            rows = []
            for line in data.get("klines") or []:
                p = str(line).split(",")
                if len(p) < 6:
                    continue
                try:
                    rows.append((p[0][:10], float(p[1]), float(p[2]),
                                 float(p[3]), float(p[4]), float(p[5])))
                except (TypeError, ValueError):
                    continue
            if rows:
                return rows[-n:]
        except Exception:
            continue
    return []


def _yahoo_screener_rows(start, count=250):
    if not _yahoo_probe() or not _src_ok("yahoo"):
        return []
    hdr = {"User-Agent": UA["User-Agent"],
           "Accept": "application/json, text/plain, */*"}
    url = YAHOO_SCREENER_URL.format(count=count, start=start)
    try:
        raw = _http(url, hdr, timeout=8)
        data = json.loads(raw.decode("utf-8", "replace"))
        res = (data.get("finance") or {}).get("result") or []
        _src_mark("yahoo", True)
        return (res[0].get("quotes") or []) if res else []
    except Exception:
        _src_mark("yahoo", False)
        return []


def _fetch_us_universe_nasdaq(limit=150):
    """东财/Yahoo 都不可用时的 Nasdaq screener 兜底(海外源, 当前可能不可达)。"""
    if not _src_ok("nasdaq"):
        return []
    hdr = {"User-Agent": UA["User-Agent"], "Referer": "https://www.nasdaq.com/",
           "Accept": "application/json, text/plain, */*"}
    try:
        raw = _http(NASDAQ_SCREENER_URL, hdr, timeout=12)
        data = json.loads(raw.decode("utf-8", "replace"))
        _src_mark("nasdaq", True)
    except Exception:
        _src_mark("nasdaq", False)
        return []
    rows = (((data.get("data") or {}).get("rows")) or [])
    out = []
    for r in rows:
        sym = str(r.get("symbol") or "").strip()
        price = _us_money(r.get("lastsale"))
        volume = _us_money(r.get("volume")) or 0
        cap = _us_money(r.get("marketCap")) or 0
        if not sym or price is None or price <= 0 or volume <= 0:
            continue
        out.append({
            "symbol": "us" + sym, "code": sym,
            "name": str(r.get("name") or sym), "price": price,
            "pct": _us_money(r.get("pctchange")), "amount": volume * price,
            "volume": volume, "high": None, "low": None, "open": None,
            "market_cap": cap, "sector": r.get("sector"),
            "industry": r.get("industry"),
            "turnover": None, "market": "us",
        })
    out.sort(key=lambda x: x["amount"], reverse=True)
    return out[:limit]


def _fetch_us_universe_yahoo(limit=150):
    """Yahoo 预置筛选(most_actives)美股列表(预留海外源, 需可访问 Yahoo)。"""
    out = []
    seen = set()
    start = 0
    while len(out) < limit and start < 1000:
        page = _yahoo_screener_rows(start, 250)
        if not page:
            break
        for r in page:
            sym = str(r.get("symbol") or "").strip().upper()
            price = _to_float(r.get("regularMarketPrice"))
            if not sym or price is None or price <= 0 or sym in seen:
                continue
            seen.add(sym)
            vol = _to_float(r.get("regularMarketVolume"), 0) or 0
            adv10 = _to_float(r.get("averageDailyVolume10Day"))
            shares = _to_float(r.get("sharesOutstanding"))
            lb = round(vol / adv10, 2) if adv10 and adv10 > 0 else None
            hs = round(vol / shares * 100.0, 3) if shares and shares > 0 else None
            out.append({
                "symbol": "us" + sym, "code": sym,
                "name": str(r.get("longName") or r.get("shortName") or sym),
                "price": price,
                "pct": _to_float(r.get("regularMarketChangePercent")),
                "amount": vol * price,
                "volume": vol,
                "high": _to_float(r.get("regularMarketDayHigh")),
                "low": _to_float(r.get("regularMarketDayLow")),
                "open": _to_float(r.get("regularMarketOpen")),
                "prev_close": _to_float(r.get("regularMarketPreviousClose")),
                "market_cap": _to_float(r.get("marketCap"), 0) or 0,
                "pe": _to_float(r.get("trailingPE")),
                "pb": _to_float(r.get("priceToBook")),
                "lb": lb, "hs": hs,
                "shares": shares,
                "sector": r.get("sector"),
                "industry": r.get("industry"),
                "turnover": None, "market": "us",
            })
        if len(page) < 250:
            break
        start += 250
    out.sort(key=lambda x: x["amount"], reverse=True)
    return out[:limit]


def fetch_us_universe(limit=150):
    """美股池: 默认 Yahoo; Yahoo 不可达时自动回退东方财富(国内直连)。

    FINA_US_SOURCE=em 可强制东财优先; Yahoo 地址可用 FINA_YAHOO_BASE 替换。
    """
    if US_SOURCE == "em":
        out = _fetch_us_universe_em(limit)
        if out:
            return out
    out = _fetch_us_universe_yahoo(limit)
    if out:
        return out
    out = _fetch_us_universe_em(limit)
    if out:
        return out
    return _fetch_us_universe_nasdaq(limit)


def _yahoo_daily_bars(sym, n=320):
    if not _yahoo_probe() or not _src_ok("yahoo"):
        return []
    url_sym = urllib.parse.quote(str(sym).replace(".", "-"), safe="")
    rng = "6mo" if n <= 60 else "2y"
    try:
        raw = _http(YAHOO_DAILY_URL.format(sym=url_sym, rng=rng), UA, timeout=8)
        res = ((json.loads(raw.decode("utf-8", "replace")).get("chart") or {})
               .get("result") or [])
    except Exception:
        _src_mark("yahoo", False)
        return []
    if not res:
        return []
    meta = res[0].get("meta") or {}
    ts = res[0].get("timestamp") or []
    q = (res[0].get("indicators", {}).get("quote") or [{}])[0]
    closes = q.get("close") or []
    opens = q.get("open") or []
    highs = q.get("high") or []
    lows = q.get("low") or []
    vols = q.get("volume") or []
    off = int(meta.get("gmtoffset") or 0)
    out = []
    for i, t in enumerate(ts):
        c = closes[i] if i < len(closes) else None
        if c is None:
            continue
        o = opens[i] if i < len(opens) else c
        h = highs[i] if i < len(highs) else c
        l = lows[i] if i < len(lows) else c
        v = vols[i] if i < len(vols) else 0
        if None in (o, h, l) or c <= 0:
            continue
        date = time.strftime("%Y-%m-%d", time.gmtime(float(t) + off))
        out.append((date, float(o), float(c), float(h), float(l), float(v or 0)))
    out.sort(key=lambda x: x[0])
    if out:
        _src_mark("yahoo", True)
    return out[-n:]


def _nasdaq_daily_bars(sym, n=320):
    if not _src_ok("nasdaq"):
        return []
    fromdate = time.strftime("%Y-%m-%d", time.localtime(time.time() - max(60, n * 2) * 86400))
    hdr = {"User-Agent": UA["User-Agent"], "Referer": "https://www.nasdaq.com/",
           "Accept": "application/json, text/plain, */*"}
    try:
        raw = _http(NASDAQ_HIST_URL.format(sym=sym, fromdate=fromdate, n=n),
                    hdr, timeout=10)
        data = json.loads(raw.decode("utf-8", "replace"))
    except Exception:
        _src_mark("nasdaq", False)
        return []
    rows = (((data.get("data") or {}).get("tradesTable") or {}).get("rows") or [])
    out = []
    for r in rows:
        try:
            dt = time.strptime(str(r.get("date") or ""), "%m/%d/%Y")
            date = time.strftime("%Y-%m-%d", dt)
        except Exception:
            continue
        c = _us_money(r.get("close"))
        if c is None:
            continue
        out.append((date, _us_money(r.get("open")) or c, c,
                    _us_money(r.get("high")) or c, _us_money(r.get("low")) or c,
                    _us_money(r.get("volume")) or 0))
    out.sort(key=lambda x: x[0])
    if out:
        _src_mark("nasdaq", True)
    return out[-n:]


def _fetch_us_bars_src(sym, n=320):
    """美股日K: 默认 Yahoo; 不可达时自动回退东财(国内直连)/Nasdaq。"""
    ticker = str(sym)
    if ticker.startswith("us") and len(ticker) > 2:
        ticker = ticker[2:]
    if US_SOURCE != "em":
        bars = _yahoo_daily_bars(ticker, n)
        if bars:
            return bars, "yahoo"
    bars = _fetch_em_us_bars(ticker, n, _EM_US_MARKET.get(ticker.upper()))
    if bars:
        return bars, "eastmoney"
    try:
        bars = _yahoo_daily_bars(ticker, n)
        if bars:
            return bars, "yahoo"
    except Exception:
        _src_mark("yahoo", False)
    try:
        bars = _nasdaq_daily_bars(ticker, n)
        if bars:
            return bars, "nasdaq"
    except Exception:
        _src_mark("nasdaq", False)
    return [], ""


def fetch_us_bars(sym, n=320):
    return _fetch_us_bars_src(sym, n)[0]


def fetch_us_index_bars(n=320):
    if US_SOURCE != "em":
        for sym in ("^GSPC", "SPY"):
            bars = _yahoo_daily_bars(sym, n)
            if bars:
                return bars
    bars = _fetch_em_index_bars(n)
    if bars:
        return bars
    for sym in ("^GSPC", "SPY"):
        bars = _yahoo_daily_bars(sym, n)
        if bars:
            return bars
    return []


def fetch_index_bars(n=320):
    for sym in (INDEX_SYMBOL, "sh000001"):
        bars = fetch_daily_bars(sym, n)
        if bars:
            return bars
    return []


def _load_cache(path=CACHE_FILE):
    try:
        with open(path, "r", encoding="utf-8") as f:
            data = json.load(f)
        if data.get("_version") != CACHE_VERSION:
            return {"bars": {}, "miss": {}}
        return {"bars": data.get("bars") or {}, "miss": data.get("miss") or {}}
    except Exception:
        return {"bars": {}, "miss": {}}


def _save_cache(cache, path=CACHE_FILE):
    try:
        cutoff = time.time() - 7 * 86400
        bars = {k: v for k, v in (cache.get("bars") or {}).items()
                if (_to_float(v.get("ts"), 0) or 0) >= cutoff}
        miss = {k: ts for k, ts in (cache.get("miss") or {}).items()
                if (_to_float(ts, 0) or 0) >= cutoff}
        payload = {
            "_version": CACHE_VERSION,
            "_saved_at": time.strftime("%Y-%m-%d %H:%M:%S"),
            "bars": bars,
            "miss": miss,
        }
        tmp = path + ".tmp"
        with open(tmp, "w", encoding="utf-8") as f:
            json.dump(payload, f, ensure_ascii=False, separators=(",", ":"))
        os.replace(tmp, path)
    except Exception:
        pass


def fetch_universe_bars(symbols, n=320, cache=None, workers=4,
                        progress_cb=None, cancel_event=None, market="a"):
    """并发抓取股票/币种日K; 返回 (bars_by_symbol, cache_hits, sources)。"""
    cache = cache if cache is not None else {"bars": {}, "miss": {}}
    now = time.time()
    result = {}
    sources = {"tencent": 0, "sina": 0, "binance": 0, "okx": 0,
               "eastmoney": 0, "yahoo": 0, "nasdaq": 0}
    hits = 0
    fails = 0
    lock = threading.Lock()
    throttle_lock = threading.Lock()
    tstate = {"fails": 0, "off_until": 0.0}

    def task(sym):
        entry = cache["bars"].get(sym)
        if entry and now - float(entry.get("ts") or 0) < CACHE_TTL \
                and int(entry.get("n") or 0) >= int(n * 0.8):
            try:
                return sym, [tuple(r) for r in entry.get("rows") or []], entry.get("src") or "tencent", True
            except Exception:
                pass
        miss = cache["miss"].get(sym)
        if miss and now - float(miss) < MISS_TTL:
            return sym, [], "", False
        _check(cancel_event)
        with throttle_lock:
            time.sleep(0.02 + random.random() * 0.04)
        if market == "crypto":
            bars, src = _fetch_crypto_bars_src(sym[2:], n)
            tencent_ok = False
            use_tencent = False
        elif market == "us":
            bars, src = _fetch_us_bars_src(sym[2:], n)
            tencent_ok = False
            use_tencent = False
        else:
            with lock:
                use_tencent = time.time() >= tstate["off_until"]
            bars, src, tencent_ok = _fetch_bars_with_source(
                sym, n, prefer_tencent=use_tencent, throttle=False)
        if use_tencent:
            with lock:
                if tencent_ok:
                    tstate["fails"] = 0
                else:
                    tstate["fails"] += 1
                    if tstate["fails"] >= 5:
                        tstate["off_until"] = time.time() + 600.0
        if bars:
            cache["bars"][sym] = {
                "asof": bars[-1][0],
                "ts": time.time(),
                "n": len(bars),
                "src": src,
                "rows": [[b[0], round(b[1], 10), round(b[2], 10),
                          round(b[3], 10), round(b[4], 10), round(b[5], 6)] for b in bars],
            }
            cache["miss"].pop(sym, None)
            return sym, bars, src, False
        cache["miss"][sym] = time.time()
        return sym, [], "", False

    total = len(symbols)
    with ThreadPoolExecutor(max_workers=max(1, workers)) as ex:
        futs = [ex.submit(task, s) for s in symbols]
        for i, fut in enumerate(as_completed(futs)):
            _check(cancel_event)
            try:
                sym, bars, src, hit = fut.result()
            except Cancelled:
                raise
            except Exception:
                continue
            if bars:
                with lock:
                    result[sym] = bars
                    if hit:
                        hits += 1
                    if src in sources:
                        sources[src] += 1
            else:
                with lock:
                    fails += 1
            if market == "crypto":
                msg = (f"日K {i + 1}/{total} · 缓存 {hits} · 币安 {sources['binance']}"
                       f" · 欧易 {sources['okx']} · 失败 {fails}")
            elif market == "us":
                msg = (f"日K {i + 1}/{total} · 缓存 {hits} · 东财 {sources['eastmoney']}"
                       f" · Yahoo {sources['yahoo']} · 失败 {fails}")
            else:
                msg = (f"日K {i + 1}/{total} · 缓存 {hits} · 腾讯 {sources['tencent']}"
                       f" · 新浪 {sources['sina']} · 失败 {fails}")
            _emit(progress_cb, "bars", i + 1, total, msg)
    return result, hits, sources


# ---------------------------------------------------------------------------
# 因子计算
# ---------------------------------------------------------------------------

def _forward_return_dates(bars_by_date, dates, di, horizon, entry_lag=1,
                          return_mode="open_to_close"):
    """按面板交易日历对齐前瞻收益; 停牌/缺失日返回 None, 不跨日填补。"""
    entry_di = di + entry_lag
    exit_di = di + horizon
    if entry_di >= len(dates) or exit_di >= len(dates):
        return None
    entry_bar = bars_by_date.get(dates[entry_di])
    exit_bar = bars_by_date.get(dates[exit_di])
    if entry_bar is None or exit_bar is None:
        return None
    entry = entry_bar[1] if return_mode == "open_to_close" else entry_bar[2]
    exit_price = exit_bar[2]
    if entry is None or entry <= 0 or exit_price is None:
        return None
    return exit_price / entry - 1.0


def _entry_gap(bars_by_date, dates, di, entry_lag=1):
    """信号日收盘 -> 次日开盘的跳空幅度; 缺失返回 None。"""
    if di + entry_lag >= len(dates):
        return None
    cur = bars_by_date.get(dates[di])
    ent = bars_by_date.get(dates[di + entry_lag])
    if cur is None or ent is None:
        return None
    c, o = cur[2], ent[1]
    if not c or c <= 0 or o is None or o <= 0:
        return None
    return o / c - 1.0


def _indicators(bars):
    n = len(bars)
    d = [b[0] for b in bars]
    o = [b[1] for b in bars]
    c = [b[2] for b in bars]
    h = [b[3] for b in bars]
    l = [b[4] for b in bars]
    v = [b[5] for b in bars]
    r = [None] * n
    logr = [None] * n
    for i in range(1, n):
        if c[i - 1] > 0 and c[i] > 0:
            r[i] = c[i] / c[i - 1] - 1.0
            logr[i] = math.log(c[i] / c[i - 1])

    tr = [None] * n
    for i in range(n):
        if i == 0:
            tr[i] = h[i] - l[i]
        else:
            tr[i] = max(h[i] - l[i], abs(h[i] - c[i - 1]), abs(l[i] - c[i - 1]))
    atr = [None] * n
    if n >= 14:
        atr[13] = sum(tr[:14]) / 14.0
        for i in range(14, n):
            atr[i] = (atr[i - 1] * 13.0 + tr[i]) / 14.0

    ema12 = [None] * n
    ema26 = [None] * n
    if n:
        ema12[0] = ema26[0] = c[0]
        for i in range(1, n):
            ema12[i] = ema12[i - 1] + (c[i] - ema12[i - 1]) * 2.0 / 13.0
            ema26[i] = ema26[i - 1] + (c[i] - ema26[i - 1]) * 2.0 / 27.0
    macd = [None if ema12[i] is None else ema12[i] - ema26[i] for i in range(n)]
    signal = [None] * n
    if n:
        signal[0] = macd[0]
        for i in range(1, n):
            signal[i] = signal[i - 1] + (macd[i] - signal[i - 1]) * 2.0 / 10.0

    ag = [0.0] * n
    al = [0.0] * n
    rsi = [None] * n
    if n > 14:
        ag[14] = sum(max(r[i] or 0.0, 0.0) for i in range(1, 15)) / 14.0
        al[14] = sum(max(-(r[i] or 0.0), 0.0) for i in range(1, 15)) / 14.0
        for i in range(15, n):
            ag[i] = (ag[i - 1] * 13.0 + max(r[i] or 0.0, 0.0)) / 14.0
            al[i] = (al[i - 1] * 13.0 + max(-(r[i] or 0.0), 0.0)) / 14.0
        for i in range(14, n):
            rsi[i] = 100.0 if al[i] <= 0 else 100.0 - 100.0 / (1.0 + ag[i] / al[i])

    obv = [0.0] * n
    for i in range(1, n):
        obv[i] = obv[i - 1] + (v[i] if (r[i] or 0.0) > 0 else
                               (-v[i] if (r[i] or 0.0) < 0 else 0.0))
    return d, o, c, h, l, v, r, logr, atr, macd, signal, rsi, obv


def _mfi(o, h, l, c, v, i, window=14):
    if i < window:
        return None
    pos = neg = 0.0
    for j in range(i - window + 1, i + 1):
        tp = (h[j] + l[j] + c[j]) / 3.0
        tpp = (h[j - 1] + l[j - 1] + c[j - 1]) / 3.0
        raw = tp * v[j]
        if tp > tpp:
            pos += raw
        elif tp < tpp:
            neg += raw
    if pos + neg <= 0:
        return None
    ratio = pos / neg if neg > 0 else 1e9
    return ((100.0 - 100.0 / (1.0 + ratio)) - 50.0) / 50.0


def _roll_mean_std(xs, k):
    """滑窗均值/样本标准差(有效值), O(n); 返回 [(n, mean, std) 或 None]。"""
    n = len(xs)
    cnt = [0] * (n + 1)
    s1 = [0.0] * (n + 1)
    s2 = [0.0] * (n + 1)
    for i in range(n):
        a = xs[i]
        av = a is not None and math.isfinite(a)
        cnt[i + 1] = cnt[i] + (1 if av else 0)
        s1[i + 1] = s1[i] + (a if av else 0.0)
        s2[i + 1] = s2[i] + (a * a if av else 0.0)
    out = [None] * n
    for i in range(k - 1, n):
        j = i - k + 1
        m = cnt[i + 1] - cnt[j]
        if not m:
            continue
        mean = (s1[i + 1] - s1[j]) / m
        std = None
        if m > 1:
            var = (s2[i + 1] - s2[j] - m * mean * mean) / (m - 1)
            std = math.sqrt(var) if var > 0 else 0.0
        out[i] = (m, mean, std)
    return out


def _roll_corr(xs, ys, k):
    """滑窗成对完整 Pearson 相关, O(n)。"""
    n = len(xs)
    cnt = [0] * (n + 1)
    sx = [0.0] * (n + 1)
    sy = [0.0] * (n + 1)
    sxx = [0.0] * (n + 1)
    syy = [0.0] * (n + 1)
    sxy = [0.0] * (n + 1)
    for i in range(n):
        a, b = xs[i], ys[i]
        ok = (a is not None and b is not None
              and math.isfinite(a) and math.isfinite(b))
        cnt[i + 1] = cnt[i] + (1 if ok else 0)
        if ok:
            sx[i + 1] = sx[i] + a
            sy[i + 1] = sy[i] + b
            sxx[i + 1] = sxx[i] + a * a
            syy[i + 1] = syy[i] + b * b
            sxy[i + 1] = sxy[i] + a * b
        else:
            sx[i + 1], sy[i + 1] = sx[i], sy[i]
            sxx[i + 1], syy[i + 1], sxy[i + 1] = sxx[i], syy[i], sxy[i]
    out = [None] * n
    for i in range(k - 1, n):
        j = i - k + 1
        m = cnt[i + 1] - cnt[j]
        if m < 5:
            continue
        ax = sx[i + 1] - sx[j]
        ay = sy[i + 1] - sy[j]
        vx = sxx[i + 1] - sxx[j] - ax * ax / m
        vy = syy[i + 1] - syy[j] - ay * ay / m
        if vx <= 0 or vy <= 0:
            continue
        cov = sxy[i + 1] - sxy[j] - ax * ay / m
        out[i] = cov / math.sqrt(vx * vy)
    return out


def _roll_mean(xs, k):
    stats = _roll_mean_std(xs, k)
    return [None if s is None else s[1] for s in stats]


def _roll_skew_kurt(xs, k):
    """滑窗偏度/超额峰度(总体矩), O(n)。"""
    n = len(xs)
    cnt = [0] * (n + 1)
    s1 = [0.0] * (n + 1)
    s2 = [0.0] * (n + 1)
    s3 = [0.0] * (n + 1)
    s4 = [0.0] * (n + 1)
    for i in range(n):
        a = xs[i]
        ok = a is not None and math.isfinite(a)
        cnt[i + 1] = cnt[i] + (1 if ok else 0)
        if ok:
            a2 = a * a
            s1[i + 1] = s1[i] + a
            s2[i + 1] = s2[i] + a2
            s3[i + 1] = s3[i] + a2 * a
            s4[i + 1] = s4[i] + a2 * a2
        else:
            s1[i + 1], s2[i + 1] = s1[i], s2[i]
            s3[i + 1], s4[i + 1] = s3[i], s4[i]
    out = [None] * n
    for i in range(k - 1, n):
        j = i - k + 1
        m = cnt[i + 1] - cnt[j]
        if m < 5:
            continue
        m1 = (s1[i + 1] - s1[j]) / m
        m2 = (s2[i + 1] - s2[j]) / m - m1 * m1
        if m2 <= 0:
            continue
        m3 = (s3[i + 1] - s3[j]) / m - 3 * m1 * (s2[i + 1] - s2[j]) / m + 2 * m1 ** 3
        m4 = ((s4[i + 1] - s4[j]) / m - 4 * m1 * (s3[i + 1] - s3[j]) / m
              + 6 * m1 * m1 * (s2[i + 1] - s2[j]) / m - 3 * m1 ** 4)
        sd = math.sqrt(m2)
        out[i] = (m3 / (sd ** 3), m4 / (m2 * m2) - 3.0)
    return out


def _roll_slope(ys, k):
    """滑窗 OLS 斜率, O(n)。"""
    n = len(ys)
    s1 = [0.0] * (n + 1)
    sj = [0.0] * (n + 1)
    for i in range(n):
        a = ys[i]
        s1[i + 1] = s1[i] + a
        sj[i + 1] = sj[i] + i * a
    den = k * (k * k - 1) / 12.0
    out = [None] * n
    for i in range(k - 1, n):
        j = i - k + 1
        sy = s1[i + 1] - s1[j]
        sjy = sj[i + 1] - sj[j]
        mean = sy / k
        num = sjy - j * sy - k * (k - 1) / 2.0 * mean
        out[i] = num / den if den else None
    return out


def _roll_beta(xs, ys, k):
    """滑窗 beta = cov(x,y)/var(y), 成对完整样本, O(n)。"""
    n = len(xs)
    cnt = [0] * (n + 1)
    sx = [0.0] * (n + 1)
    sy = [0.0] * (n + 1)
    syy = [0.0] * (n + 1)
    sxy = [0.0] * (n + 1)
    for i in range(n):
        a, b = xs[i], ys[i]
        ok = (a is not None and b is not None
              and math.isfinite(a) and math.isfinite(b))
        cnt[i + 1] = cnt[i] + (1 if ok else 0)
        if ok:
            sx[i + 1] = sx[i] + a
            sy[i + 1] = sy[i] + b
            syy[i + 1] = syy[i] + b * b
            sxy[i + 1] = sxy[i] + a * b
        else:
            sx[i + 1], sy[i + 1] = sx[i], sy[i]
            syy[i + 1], sxy[i + 1] = syy[i], sxy[i]
    out = [None] * n
    for i in range(k - 1, n):
        j = i - k + 1
        m = cnt[i + 1] - cnt[j]
        if m < 30:
            continue
        ax = sx[i + 1] - sx[j]
        ay = sy[i + 1] - sy[j]
        vy = syy[i + 1] - syy[j] - ay * ay / m
        if vy <= 0:
            continue
        cov = sxy[i + 1] - sxy[j] - ax * ay / m
        out[i] = cov / vy
    return out


def compute_symbol_factors(bars, index_ret_by_date, index_ret20_by_date):
    """返回 {date: {factor_key: value}}, 只使用当日及以前的数据。
    滑窗统计使用前缀和 O(1)/日, 避免逐日重新扫描窗口。"""
    n = len(bars)
    if n < 70:
        return {}
    d, o, c, h, l, v, r, logr, atr, macd, signal, rsi, obv = _indicators(bars)
    logc = [math.log(x) if x > 0 else 0.0 for x in c]
    ideal = [index_ret_by_date.get(x) for x in d]

    ret_ = {k: _roll_mean_std(c, k) for k in (5, 10, 20, 60)}
    vol_ = {k: _roll_mean_std(logr, k) for k in (5, 20, 60)}
    dv_ = _roll_mean([None if x is None else min(x, 0.0) ** 2 for x in logr], 20)
    vol5_ = _roll_mean_std(v, 5)
    vol20_ = _roll_mean_std(v, 20)
    amihud_raw = [None if r[j] is None or c[j] <= 0 or v[j] <= 0
                  else abs(r[j]) / (c[j] * v[j] * 100.0) for j in range(n)]
    amihud_ = _roll_mean(amihud_raw, 20)
    dlogv = [None] + [math.log((v[j] + 1.0) / (v[j - 1] + 1.0)) for j in range(1, n)]
    pv_ = _roll_corr(r, dlogv, 20)
    autoc_ = _roll_corr(logr, [None] + logr[:-1], 20)
    cp_raw = [((c[j] - l[j]) / (h[j] - l[j])) if h[j] > l[j] else None for j in range(n)]
    cp5_ = _roll_mean(cp_raw, 5)
    cp20_ = _roll_mean(cp_raw, 20)
    up_sh = [(h[j] - max(o[j], c[j])) / c[j] for j in range(n)]
    lo_sh = [(min(o[j], c[j]) - l[j]) / c[j] for j in range(n)]
    up_sh_ = _roll_mean(up_sh, 20)
    lo_sh_ = _roll_mean(lo_sh, 20)
    posday_ = _roll_mean([1.0 if (r[j] or 0.0) > 0 else 0.0 for j in range(n)], 20)
    gap_raw = [None] + [((o[j] - c[j - 1]) / c[j - 1]) if c[j - 1] > 0 else None
                        for j in range(1, n)]
    gap_ = _roll_mean(gap_raw, 20)
    sl_ = _roll_slope(logc, 20)
    vtrend_ = _roll_slope([math.log(x + 1.0) for x in v], 20)
    sk_ = _roll_skew_kurt(logr, 20)
    beta_ = _roll_beta(r, ideal, 60)
    corr_ = _roll_corr(r, ideal, 60)
    out = {}

    for i in range(60, n):
        f = {}
        base = c[i]

        # 动量 / 趋势
        f["ret_1"] = r[i]
        for k in (5, 10, 20, 60):
            if i >= k:
                f[f"ret_{k}"] = base / c[i - k] - 1.0
        for k in (5, 10, 20):
            if i >= k + 1:
                f[f"mom_{k}_1"] = c[i - 1] / c[i - k - 1] - 1.0
        for k in (5, 10, 20, 60):
            s = ret_[k][i]
            if s and s[1]:
                f[f"ma_dev_{k}"] = base / s[1] - 1.0
        f["slope_20"] = sl_[i]
        if rsi[i] is not None:
            f["rsi_14"] = (rsi[i] - 50.0) / 50.0
        if macd[i] is not None and signal[i] is not None:
            f["macd_hist"] = (macd[i] - signal[i]) / base
        f["max_ret_20"] = max(r[i - 19:i + 1])

        # 波动
        for k in (5, 20, 60):
            s = vol_[k][i]
            if s and s[2]:
                f[f"realvol_{k}"] = s[2] * math.sqrt(TRADING_DAYS)
        if dv_[i]:
            f["downvol_20"] = math.sqrt(dv_[i]) * math.sqrt(TRADING_DAYS)
        if atr[i] is not None:
            f["atr_14"] = atr[i] / base
        f["mdd_60"] = _mdd(c[i - 59:i + 1])
        f["range_20"] = (max(h[i - 19:i + 1]) - min(l[i - 19:i + 1])) / base
        if sk_[i]:
            f["skew_20"], f["kurt_20"] = sk_[i]
        f["autocorr_20"] = autoc_[i]

        # 量能 / 流动性
        s5, s20 = vol5_[i], vol20_[i]
        if s5 and s20 and s20[1]:
            f["volratio_5"] = s5[1] / s20[1]
        f["vol_trend_20"] = vtrend_[i]
        if s20 and s20[1] and s20[2] is not None:
            f["vol_cv_20"] = s20[2] / s20[1]
        if amihud_[i] is not None:
            f["amihud_20"] = amihud_[i] * 1e9
        f["pv_corr_20"] = pv_[i]
        if i >= 20 and s20 and s20[1]:
            f["obv_slope_20"] = (obv[i] - obv[i - 20]) / (s20[1] * 20.0)
        f["mfi_14"] = _mfi(o, h, l, c, v, i)

        # 形态
        f["close_pos_5"] = cp5_[i]
        f["close_pos_20"] = cp20_[i]
        f["upper_shadow_20"] = up_sh_[i]
        f["lower_shadow_20"] = lo_sh_[i]
        f["pos_day_ratio_20"] = posday_[i]
        f["gap_20"] = gap_[i]

        # 市场
        beta = beta_[i]
        f["beta_60"] = beta
        f["corr_60"] = corr_[i]
        if beta is not None and i >= 20:
            idx20 = index_ret20_by_date.get(d[i])
            if idx20 is not None:
                f["resid_mom_20"] = (base / c[i - 20] - 1.0) - beta * idx20

        out[d[i]] = {k: v for k, v in f.items()
                     if v is not None and math.isfinite(v)}
    return out


def _index_maps(index_bars):
    ret = {}
    ret20 = {}
    c = [b[2] for b in index_bars]
    d = [b[0] for b in index_bars]
    for i in range(1, len(c)):
        if c[i - 1] > 0:
            ret[d[i]] = c[i] / c[i - 1] - 1.0
        if i >= 20 and c[i - 20] > 0:
            ret20[d[i]] = c[i] / c[i - 20] - 1.0
    return ret, ret20


class Panel:
    __slots__ = ("dates", "symbols", "values", "forward", "volumes", "gaps",
                 "ranks", "fwd_rank")

    def __init__(self, dates, symbols, values, forward, volumes, gaps=None):
        self.dates = dates
        self.symbols = symbols
        self.values = values
        self.forward = forward
        self.volumes = volumes
        self.gaps = gaps
        self.ranks = None
        self.fwd_rank = None


def build_panel(bars_by_symbol, index_bars, lookback=250, horizon=1,
                entry_lag=1, return_mode="open_to_close",
                progress_cb=None, cancel_event=None):
    index_ret, index_ret20 = _index_maps(index_bars)
    if index_bars:
        all_dates = sorted({b[0] for b in index_bars})
    else:
        all_dates = sorted({b[0] for rows in bars_by_symbol.values() for b in rows})
    dates = all_dates[-lookback:] if lookback and lookback > 0 else all_dates
    di_map = {d: i for i, d in enumerate(dates)}
    symbols = [s for s in bars_by_symbol if bars_by_symbol[s]]
    S = len(symbols)
    D = len(dates)
    values = {k: array("d", [NAN]) * (D * S) for k in FACTOR_KEYS}
    forward = array("d", [NAN]) * (D * S)
    volumes = array("d", [NAN]) * (D * S)
    gaps = array("d", [NAN]) * (D * S)

    for si, sym in enumerate(symbols):
        _check(cancel_event)
        bars = bars_by_symbol[sym]
        series = compute_symbol_factors(bars, index_ret, index_ret20)
        by_date = {b[0]: b for b in bars}
        for di, date in enumerate(dates):
            off = di * S + si
            row = series.get(date)
            if row:
                for key, val in row.items():
                    values[key][off] = val
            bar = by_date.get(date)
            if bar is not None and bar[5] is not None:
                volumes[off] = bar[5]
            fwd = _forward_return_dates(by_date, dates, di, horizon,
                                        entry_lag, return_mode)
            gap = _entry_gap(by_date, dates, di, entry_lag)
            if gap is not None:
                gaps[off] = gap
            # A股/ETF 次日开盘即涨停时无法买入, 不计入前瞻收益/IC
            if fwd is not None and gap is not None and sym.startswith(("sh", "sz", "bj")):
                if gap >= _price_limit(sym) / 100.0 - 0.005:
                    fwd = None
            if fwd is not None:
                forward[off] = fwd
        if (si + 1) % 20 == 0 or si + 1 == S:
            _emit(progress_cb, "panel", si + 1, S, f"计算因子 {si + 1}/{S}")
    return Panel(dates, symbols, values, forward, volumes, gaps)


def build_rank_panel(panel, progress_cb=None, cancel_event=None):
    """一次性构建日期×股票的横截面分位排名, 供 IC/去重/打分复用。"""
    if panel.ranks is not None:
        return panel.ranks
    S = len(panel.symbols)
    D = len(panel.dates)
    ranks = {k: array("d", [NAN]) * (D * S) for k in FACTOR_KEYS}
    fwd_rank = array("d", [NAN]) * (D * S)
    for di in range(D):
        _check(cancel_event)
        off = di * S
        fr = _percentile_rank([panel.forward[off + si] for si in range(S)])
        for si, r in enumerate(fr):
            if r is not None:
                fwd_rank[off + si] = r
        for key in FACTOR_KEYS:
            rk = _percentile_rank([panel.values[key][off + si] for si in range(S)])
            arr = ranks[key]
            for si, r in enumerate(rk):
                if r is not None:
                    arr[off + si] = r
        if (di + 1) % 20 == 0 or di + 1 == D:
            _emit(progress_cb, "ranks", di + 1, D, f"横截面排名 {di + 1}/{D}")
    panel.ranks = ranks
    panel.fwd_rank = fwd_rank
    return ranks


# ---------------------------------------------------------------------------
# IC / 权重 / 样本外
# ---------------------------------------------------------------------------

def compute_ic(panel, factor_keys=None, date_indices=None, min_names=20, horizon=1):
    keys = factor_keys or FACTOR_KEYS
    S = len(panel.symbols)
    D = len(panel.dates)
    if date_indices is None:
        date_indices = list(range(D))
    if horizon > 1:
        date_indices = date_indices[::horizon]
    ranks = build_rank_panel(panel)
    fwd_rank = panel.fwd_rank
    stats = {k: {"ics": [], "pairs": 0, "by_date": {}} for k in keys}
    used = []
    for di in date_indices:
        off = di * S
        fwd = [fwd_rank[off + si] for si in range(S)]
        if sum(1 for x in fwd if math.isfinite(x)) < min_names:
            continue
        used.append(di)
        for key in keys:
            arr = ranks[key]
            ic, n = _rank_ic_at(arr, fwd, off, S, min_names)
            if ic is not None:
                stats[key]["ics"].append((di, ic))
                stats[key]["pairs"] += n
                stats[key]["by_date"][di] = n
    return stats, used


def analyze_volume(panel, horizon=1, min_n=200):
    """回测 当日量/前2日量 对次日收益的区分度: 分桶 + 阈值扫描 + 日度RankIC。"""
    S = len(panel.symbols)
    D = len(panel.dates)
    date_indices = list(range(D))
    if horizon > 1:
        date_indices = date_indices[::horizon]
    by_date = []
    all_pairs = []
    for di in date_indices:
        if di < 2:
            continue
        off, off2 = di * S, (di - 2) * S
        rows = []
        for si in range(S):
            v0 = panel.volumes[off + si]
            v2 = panel.volumes[off2 + si]
            fwd = panel.forward[off + si]
            if (math.isfinite(v0) and math.isfinite(v2) and v2 > 0
                    and math.isfinite(fwd)):
                rows.append((v0 / v2, fwd))
        if len(rows) >= 20:
            by_date.append((di, rows))
            all_pairs.extend(rows)
    if len(all_pairs) < min_n:
        return {"n_dates": 0, "n_pairs": len(all_pairs), "mean_ic": None,
                "icir": None, "t": None, "baseline": None, "hit": None,
                "buckets": [], "thresholds": [], "best": None}
    ics = []
    for _di, rows in by_date:
        ic = _spearman([r for r, _f in rows], [f for _r, f in rows])
        if ic is not None:
            ics.append(ic)
    mean_ic = _mean(ics)
    std_ic = _std(ics)
    icir = mean_ic / std_ic if (mean_ic is not None and std_ic and std_ic > 0) else None
    t_ic = (mean_ic / (std_ic / math.sqrt(len(ics)))
            if (mean_ic is not None and std_ic and std_ic > 0 and ics) else None)
    rets = [f for _r, f in all_pairs]
    baseline = _mean(rets)
    base_hit = sum(1 for x in rets if x > 0) / float(len(rets))
    buckets = [(0.0, 0.5), (0.5, 0.8), (0.8, 1.0), (1.0, 1.2),
               (1.2, 1.5), (1.5, 2.0), (2.0, 3.0), (3.0, float("inf"))]
    bucket_rows = []
    for lo, hi in buckets:
        vals = [f for r, f in all_pairs if lo <= r < hi]
        if not vals:
            bucket_rows.append({"range": f"{lo:g}~{hi:g}" if hi != float("inf") else f"≥{lo:g}",
                                "n": 0, "mean": None, "hit": None,
                                "excess": None, "t": None})
            continue
        m = _mean(vals)
        sd = _std(vals)
        bucket_rows.append({
            "range": f"{lo:g}~{hi:g}" if hi != float("inf") else f"≥{lo:g}",
            "n": len(vals), "mean": m,
            "hit": sum(1 for x in vals if x > 0) / len(vals),
            "excess": (m - baseline) if (m is not None and baseline is not None) else None,
            "t": (m / (sd / math.sqrt(len(vals)))
                  if (m is not None and sd and sd > 0) else None),
        })
    thresholds = [1.0, 1.2, 1.5, 2.0, 2.5, 3.0, 4.0, 5.0]
    threshold_rows = []
    for th in thresholds:
        vals = [f for r, f in all_pairs if r >= th]
        if not vals:
            continue
        m = _mean(vals)
        sd = _std(vals)
        threshold_rows.append({
            "threshold": th, "n": len(vals), "mean": m,
            "hit": sum(1 for x in vals if x > 0) / len(vals),
            "excess": (m - baseline) if (m is not None and baseline is not None) else None,
            "t": (m / (sd / math.sqrt(len(vals)))
                  if (m is not None and sd and sd > 0) else None),
        })
    candidates = [x for x in threshold_rows
                  if x["n"] >= min_n and x["excess"] is not None and x["excess"] > 0]
    best = max(candidates, key=lambda x: x["t"] or 0) if candidates else None
    return {
        "n_dates": len(by_date), "n_pairs": len(all_pairs),
        "mean_ic": mean_ic, "icir": icir, "t": t_ic,
        "baseline": baseline, "hit": base_hit,
        "buckets": bucket_rows, "thresholds": threshold_rows, "best": best,
    }


def _subset_ic_stats(stats, date_set):
    out = {}
    for key, d in stats.items():
        ics = [(di, ic) for di, ic in d["ics"] if di in date_set]
        by_date = {di: n for di, n in d["by_date"].items() if di in date_set}
        out[key] = {"ics": ics, "pairs": sum(by_date.values()), "by_date": by_date}
    return out


def summarize_ic(stats, num_dates, num_symbols, half_life=60.0):
    rows = {}
    denom = max(1, num_dates) * max(1, num_symbols)
    for key, d in stats.items():
        pairs = d["ics"]
        ics = [ic for _, ic in pairs]
        n = len(ics)
        mean = _mean(ics)
        std = _std(ics)
        icir = mean / std if (mean is not None and std and std > 0) else None
        t = mean / (std / math.sqrt(n)) if (mean is not None and std and std > 0 and n) else None
        pos = sum(1 for x in ics if x > 0) / n if n else None
        consistency = max(pos, 1.0 - pos) if pos is not None else None

        # 近期 IC 加权: 越近的日期权重越高, 用于适配风格切换
        ew_mean = ew_std = ew_icir = None
        if pairs:
            last_di = max(di for di, _ in pairs)
            wsum = 0.0
            wmean = 0.0
            for di, ic in pairs:
                w = 0.5 ** ((last_di - di) / max(1.0, half_life))
                wsum += w
                wmean += w * ic
            if wsum > 0:
                wmean /= wsum
                wvar = sum(0.5 ** ((last_di - di) / max(1.0, half_life))
                           * (ic - wmean) ** 2 for di, ic in pairs) / wsum
                ew_mean = wmean
                ew_std = math.sqrt(wvar) if wvar > 0 else 0.0
                ew_icir = ew_mean / ew_std if ew_std and ew_std > 0 else None
        recent = ics[-20:]
        rows[key] = {
            "ics": ics, "by_date": d["by_date"], "n_dates": n,
            "mean_ic": mean, "std_ic": std, "icir": icir, "t": t,
            "pos_rate": pos, "consistency": consistency,
            "ew_mean_ic": ew_mean, "ew_icir": ew_icir,
            "recent_mean_ic": _mean(recent) if recent else None,
            "win_rate": pos,
            "coverage": d["pairs"] / denom,
        }
    return rows


def _rank_series_corr(panel, k1, k2, sample_dates, S):
    rank1 = panel.ranks[k1]
    rank2 = panel.ranks[k2]
    n = 0
    sx = sy = sxx = syy = sxy = 0.0
    for di in sample_dates:
        off = di * S
        for si in range(S):
            a = rank1[off + si]
            b = rank2[off + si]
            if math.isfinite(a) and math.isfinite(b):
                n += 1
                sx += a
                sy += b
                sxx += a * a
                syy += b * b
                sxy += a * b
    if n < 10:
        return None
    cov = sxy - sx * sy / n
    vx = sxx - sx * sx / n
    vy = syy - sy * sy / n
    if vx <= 0 or vy <= 0:
        return None
    return cov / math.sqrt(vx * vy)


def select_weights(panel, stats, date_indices, min_coverage=0.5,
                   min_abs_ic=0.01, min_t=None, min_consistency=0.55,
                   corr_cap=0.85, sign_map=None, cancel_event=None):
    S = len(panel.symbols)
    # 5 日周期 + 短回看时有效 IC 日期天然较少, 门槛随之放宽, 但不低于 8 天
    min_dates = min(20, max(8, len(date_indices) // 2))
    # 42 个因子同时检验, 样本越长越应提高 t 门槛以控制假阳性
    t_gate = min_t if min_t is not None else (2.0 if len(date_indices) >= 60 else 1.5)
    eligible = []
    reasons = {}
    for key, st in stats.items():
        why = None
        ref_mean = st["ew_mean_ic"] if st.get("ew_mean_ic") is not None else st["mean_ic"]
        ref_icir = st["ew_icir"] if st.get("ew_icir") is not None else st["icir"]
        if st["n_dates"] < min_dates:
            why = "有效IC天数不足"
        elif st["coverage"] < min_coverage:
            why = "覆盖率不足"
        elif ref_mean is None:
            why = "无有效IC"
        elif abs(ref_mean) < min_abs_ic:
            why = "|IC|过低"
        elif st["t"] is None or abs(st["t"]) < t_gate:
            why = "t值不显著"
        elif st["consistency"] is None or st["consistency"] < min_consistency:
            why = "方向不稳定"
        elif (st.get("recent_mean_ic") is not None and ref_mean is not None
              and abs(st["recent_mean_ic"]) >= 0.01
              and (st["recent_mean_ic"] > 0) != (ref_mean > 0)):
            why = "近期变号"
        elif sign_map is not None and key in sign_map and not sign_map[key]:
            why = "样本外变号"
        if why:
            reasons[key] = why
            continue
        sign = 1.0 if ref_mean > 0 else -1.0
        strength = (max(0.01, abs(ref_icir or 0.0))
                    * math.sqrt(max(0.0, st["coverage"]))
                    * st["n_dates"] / (st["n_dates"] + 20.0))
        eligible.append((key, sign, strength))
    eligible.sort(key=lambda x: x[2], reverse=True)

    sample_dates = date_indices[::max(1, len(date_indices) // 24)] or date_indices
    build_rank_panel(panel)

    kept = []
    meta = {}
    for key, sign, strength in eligible:
        _check(cancel_event)
        conflict = None
        corr_load = 0.0
        for k2, _s2, _st2 in kept:
            c = _rank_series_corr(panel, key, k2, sample_dates, S)
            if c is not None:
                if abs(c) > corr_cap:
                    conflict = (k2, c)
                    break
                corr_load += abs(c)
        if conflict:
            reasons[key] = f"与{FACTOR_DEFS[conflict[0]][0]}高相关({conflict[1]:+.2f})"
            continue
        # 与已选因子的平均相关性越高, 权重越低, 避免同类信息重复计价
        adj = strength / math.sqrt(1.0 + corr_load)
        kept.append((key, sign, adj))
        meta[key] = {"sign": sign, "strength": strength,
                     "adj_strength": adj, "corr_load": corr_load}

    total = sum(x[2] for x in kept)
    weights = {}
    for key in stats:
        if key not in meta:
            meta[key] = {"sign": 0.0, "strength": 0.0, "weight": 0.0,
                         "reason": reasons.get(key, "未入选")}
    if total > 0:
        for key, sign, strength in kept:
            weights[key] = sign * strength / total
            meta[key]["weight"] = weights[key]
            meta[key]["reason"] = "入选"
    return weights, meta


def _summarize_ic_values(ics, num_dates):
    vals = [x for x in ics if x is not None and math.isfinite(x)]
    n = len(vals)
    if not n:
        return {"n_dates": 0, "mean_ic": None, "std_ic": None,
                "icir": None, "t": None}
    mean = sum(vals) / n
    std = _std(vals)
    icir = mean / std if std and std > 0 else None
    t = mean / (std / math.sqrt(n)) if std and std > 0 else None
    return {"n_dates": n, "mean_ic": mean, "std_ic": std,
            "icir": icir, "t": t, "dates": num_dates}


def _composite(ranks, weights, off, si, min_cov=None):
    """加权分位合成, 并按可用因子总权重归一化, 避免缺失因子把分数拉向中位。"""
    total = 0.0
    abs_w = 0.0
    cov = 0
    for key, w in weights.items():
        rk = ranks[key][off + si]
        if math.isfinite(rk):
            total += w * (rk - 0.5)
            abs_w += abs(w)
            cov += 1
    if min_cov is not None and cov < min_cov:
        return None, cov
    if abs_w <= 0:
        return None, cov
    return total / abs_w, cov


def _eval_weights(panel, date_indices, weights):
    S = len(panel.symbols)
    ranks = build_rank_panel(panel)
    ics = []
    min_cov = max(1, len(weights) // 2)
    for di in date_indices:
        off = di * S
        scores, fwd = [], []
        for si in range(S):
            y = panel.forward[off + si]
            if not math.isfinite(y):
                continue
            comp, _cov = _composite(ranks, weights, off, si, min_cov=min_cov)
            if comp is None:
                continue
            scores.append(comp)
            fwd.append(y)
        if len(scores) >= 20:
            ic = _spearman(scores, fwd)
            if ic is not None:
                ics.append(ic)
    result = _summarize_ic_values(ics, len(date_indices))
    result["ics"] = ics
    return result


def _simulate_topk(panel, weights, date_indices, top_k=20, horizon=1,
                   cost=0.0015, exclude_limit=True):
    """横截面 Top-K 等权组合的样本外模拟(次日开盘成交, 计往返成本)。"""
    if not weights or not date_indices:
        return {"n_dates": 0, "top_k": top_k, "cum": None, "ann": None,
                "sharpe": None, "mdd": None, "hit": None,
                "bench_cum": None, "excess": None, "cost": cost}
    ranks = build_rank_panel(panel)
    S = len(panel.symbols)
    dates = list(date_indices)
    min_cov = max(1, len(weights) // 2)
    ret1 = panel.values.get("ret_1")
    rets, bench = [], []
    for di in dates:
        off = di * S
        scored = []
        for si in range(S):
            sym = panel.symbols[si]
            y = panel.forward[off + si]
            if not math.isfinite(y):
                continue
            if exclude_limit and ret1 is not None:
                r1 = ret1[off + si]
                if math.isfinite(r1) and r1 >= _price_limit(sym) / 100.0 - 0.0005:
                    continue
            comp, cov = _composite(ranks, weights, off, si, min_cov=min_cov)
            if comp is None:
                continue
            scored.append((comp, y))
        if len(scored) < top_k:
            continue
        scored.sort(key=lambda x: x[0], reverse=True)
        rets.append(_mean([y for _s, y in scored[:top_k]]) - cost)
        bench.append(_mean([y for _s, y in scored]) - cost)
    if not rets:
        return {"n_dates": 0, "top_k": top_k, "cum": None, "ann": None,
                "sharpe": None, "mdd": None, "hit": None,
                "bench_cum": None, "excess": None, "cost": cost}
    eq = 1.0
    peak = 1.0
    mdd = 0.0
    for r in rets:
        eq *= 1.0 + r
        peak = max(peak, eq)
        mdd = min(mdd, eq / peak - 1.0)
    beq = 1.0
    for r in bench:
        beq *= 1.0 + r
    n = len(rets)
    mean = _mean(rets)
    sd = _std(rets)
    periods = TRADING_DAYS / float(horizon)
    ann = eq ** (periods / n) - 1.0 if eq > 0 and n else None
    sharpe = (mean / sd * math.sqrt(periods)) if (mean is not None and sd and sd > 0) else None
    return {
        "n_dates": n, "top_k": top_k,
        "cum": eq - 1.0, "ann": ann, "sharpe": sharpe, "mdd": mdd,
        "hit": sum(1 for r in rets if r > 0) / float(n),
        "bench_cum": beq - 1.0, "excess": eq - beq,
        "cost": cost,
    }


def walk_forward(panel, stats, ic_dates, split=0.7, top_k=20, horizon=1,
                 exclude_limit=True, **weight_kwargs):
    n = len(ic_dates)
    if n < 20:
        return {"weights": {}, "selected": {}, "sign_map": {},
                "oos": _summarize_ic_values([], 0),
                "equal_oos": _summarize_ic_values([], 0),
                "portfolio": _simulate_topk(panel, {}, [], top_k=top_k, horizon=horizon),
                "train_dates": 0, "test_dates": 0,
                "folds": [], "oos_folds": _summarize_ic_values([], 0),
                "note": "有效IC日期不足，无法做样本外检验"}
    cut = max(10, int(n * split))
    train_dates = ic_dates[:cut]
    test_dates = ic_dates[cut:]
    train_stats = summarize_ic(_subset_ic_stats(stats, set(train_dates)),
                               len(train_dates), len(panel.symbols))
    test_subset = _subset_ic_stats(stats, set(test_dates))
    test_stats = summarize_ic(test_subset, len(test_dates), len(panel.symbols))
    sign_map = {}
    for key in stats:
        tr = train_stats.get(key) or {}
        te = test_stats.get(key) or {}
        if (tr.get("n_dates", 0) >= 8 and te.get("n_dates", 0) >= 8
                and tr.get("mean_ic") is not None and te.get("mean_ic") is not None):
            sign_map[key] = (tr["mean_ic"] > 0) == (te["mean_ic"] > 0)
    weights, meta = select_weights(panel, train_stats, train_dates, **weight_kwargs)
    if not weights or not test_dates:
        return {"weights": weights, "selected": meta, "sign_map": sign_map,
                "oos": _summarize_ic_values([], 0),
                "equal_oos": _summarize_ic_values([], 0),
                "portfolio": _simulate_topk(panel, {}, [], top_k=top_k, horizon=horizon),
                "train_dates": len(train_dates), "test_dates": len(test_dates),
                "folds": [], "oos_folds": _summarize_ic_values([], 0),
                "note": "训练集没有因子通过筛选，样本外无法评价"}
    oos = _eval_weights(panel, test_dates, weights)
    eq = {k: (1.0 if w > 0 else -1.0) / len(weights) for k, w in weights.items()}
    equal_oos = _eval_weights(panel, test_dates, eq)
    portfolio = _simulate_topk(panel, weights, test_dates,
                               top_k=top_k, horizon=horizon,
                               exclude_limit=exclude_limit)
    # 多折滚动样本外: 3 段测试窗口均落在后 50%, 训练集逐折扩张,
    # 用于判断因子组合的样本外表现是否只在某一段行情里偶然有效
    folds = []
    fold_ics = []
    if n >= 30:
        for f in range(3):
            lo = int(n * (0.5 + f / 6.0))
            hi = int(n * (0.5 + (f + 1) / 6.0)) if f < 2 else n
            tr, te = ic_dates[:lo], ic_dates[lo:hi]
            if len(tr) < 10 or len(te) < 5:
                continue
            tr_stats = summarize_ic(_subset_ic_stats(stats, set(tr)),
                                    len(tr), len(panel.symbols))
            fw, _fm = select_weights(panel, tr_stats, tr, **weight_kwargs)
            if not fw:
                folds.append({"train": len(tr), "test": len(te), "ic": None})
                continue
            ev = _eval_weights(panel, te, fw)
            folds.append({"train": len(tr), "test": len(te),
                          "ic": ev.get("mean_ic"), "t": ev.get("t")})
            fold_ics.extend(ev.get("ics") or [])
    oos_folds = _summarize_ic_values(fold_ics, n) if fold_ics else _summarize_ic_values([], 0)
    return {"weights": weights, "selected": meta, "sign_map": sign_map,
            "oos": oos, "equal_oos": equal_oos, "portfolio": portfolio,
            "train_dates": len(train_dates), "test_dates": len(test_dates),
            "folds": folds, "oos_folds": oos_folds, "note": ""}


# ---------------------------------------------------------------------------
# 最新截面打分与主流程
# ---------------------------------------------------------------------------

def _latest_di(panel, weights, min_names=20):
    S = len(panel.symbols)
    for di in range(len(panel.dates) - 1, -1, -1):
        off = di * S
        cov = 0
        for si in range(S):
            if any(math.isfinite(panel.values[k][off + si]) for k in weights):
                cov += 1
                if cov >= min_names:
                    return di
    return None


def _price_limit(symbol):
    if symbol.startswith("bj"):
        return 30.0
    if symbol[2:].startswith(("300", "301", "688", "689")):
        return 20.0
    return 10.0


def score_latest(panel, weights, universe_rows, threshold=None,
                 exclude_limit_up=True):
    if not weights or not panel.symbols:
        return []
    di = _latest_di(panel, weights)
    if di is None:
        return []
    S = len(panel.symbols)
    off = di * S
    rank_panel = build_rank_panel(panel)
    by_symbol = {r["symbol"]: r for r in universe_rows}
    rows = []
    for si, sym in enumerate(panel.symbols):
        total = 0.0
        abs_total = 0.0
        cov = 0
        cat_sum = {k: 0.0 for k, _ in CATEGORIES}
        cat_abs = {k: 0.0 for k, _ in CATEGORIES}
        contribs = []
        for key, w in weights.items():
            rk = rank_panel[key][off + si]
            if not math.isfinite(rk):
                continue
            cov += 1
            c = w * (rk - 0.5)
            total += c
            abs_total += abs(w)
            cat = FACTOR_DEFS[key][1]
            cat_sum[cat] += c
            cat_abs[cat] += abs(w)
            contribs.append((c, key))
        if cov == 0 or abs_total <= 0:
            continue
        # 原始加权分位(缺失因子已按可用权重归一化); 最终得分再做横截面分位映射
        comp = total / abs_total
        cat_comp = {cat: (cat_sum[cat] / cat_abs[cat] if cat_abs[cat] > 0 else None)
                    for cat, _label in CATEGORIES}
        contribs.sort(key=lambda x: abs(x[0]), reverse=True)
        top = []
        for c, key in contribs[:3]:
            top.append(f"{FACTOR_DEFS[key][0]}{'+' if c >= 0 else '-'}")
        ma_dev = {}
        for k in (5, 10, 20, 60):
            v = panel.values.get(f"ma_dev_{k}")
            if v is not None:
                x = v[off + si]
                if math.isfinite(x):
                    ma_dev[k] = x
        up = [str(k) for k in (5, 10, 20, 60)
              if ma_dev.get(k) is not None and ma_dev[k] >= 0]
        down = [str(k) for k in (5, 10, 20, 60)
                if ma_dev.get(k) is not None and ma_dev[k] < 0]
        parts = []
        if up:
            parts.append("上" + ",".join(up))
        if down:
            parts.append("下" + ",".join(down))
        ma_status = " ".join(parts) if parts else "—"
        ma_above = [k for k in (5, 10, 20, 60)
                    if ma_dev.get(k) is not None and ma_dev[k] >= 0]
        vol_prev2 = None
        if di >= 2:
            v0 = panel.volumes[off + si]
            v2 = panel.volumes[(di - 2) * S + si]
            if math.isfinite(v0) and math.isfinite(v2) and v2 > 0:
                vol_prev2 = v0 / v2
        u = by_symbol.get(sym, {})
        pct = u.get("pct")
        if exclude_limit_up and pct is not None and pct >= _price_limit(sym) - 0.05:
            continue
        vol20 = panel.values["realvol_20"][off + si]
        rows.append({
            "code": u.get("code") or sym[2:],
            "name": u.get("name") or "",
            "symbol": sym,
            "price": u.get("price"),
            "pct": pct,
            "amount": u.get("amount"),
            "turnover": u.get("turnover"),
            "score": None,
            "rank": 0,
            "cat_scores": {},
            "_comp": comp,
            "_cat_comp": cat_comp,
            "top": " ".join(top) if top else "—",
            "coverage": cov / float(len(weights)),
            "ma_dev": ma_dev, "ma_status": ma_status, "ma_above": ma_above,
            "vol_prev2": vol_prev2,
            "vol20": vol20 if math.isfinite(vol20) else None,
            "asof": panel.dates[di],
            "industry": u.get("industry") or u.get("sector") or "…",
        })
    rows.sort(key=lambda r: r.get("_comp") or -1e18, reverse=True)
    # 合成值映射为横截面分位得分(0~100): 阈值 85/95 才有明确统计含义
    if rows:
        pr = _percentile_rank([r.get("_comp") for r in rows])
        for r, p in zip(rows, pr):
            r["score"] = 50.0 if p is None else 100.0 * p
        for cat, _label in CATEGORIES:
            pr = _percentile_rank([(r.get("_cat_comp") or {}).get(cat) for r in rows])
            for r, p in zip(rows, pr):
                r["cat_scores"][cat] = None if p is None else 100.0 * p
        for r in rows:
            r.pop("_comp", None)
            r.pop("_cat_comp", None)
        rows.sort(key=lambda r: r["score"], reverse=True)
    for i, r in enumerate(rows):
        r["rank"] = i + 1
    if threshold is not None:
        rows = [r for r in rows if r["score"] >= threshold]
    return rows


def _evidence_ok(wf):
    oos = wf.get("oos") or {}
    pf = wf.get("portfolio") or {}
    folds = [f for f in (wf.get("folds") or []) if f.get("ic") is not None]
    fold_stable = (not folds) or (sum(1 for f in folds if f["ic"] > 0) * 2 >= len(folds))
    return bool(oos.get("mean_ic") is not None and oos["mean_ic"] > 0
                and (pf.get("excess") is None or pf["excess"] > 0)
                and fold_stable)


def annotate_advice(rows, wf, vol_cap=0.8):
    """基于因子得分、横截面排名和样本外证据, 标注次日研究候选。
    样本外 IC/组合超额不同时为正时, 不输出"强候选/候选", 最多"谨慎候选"。"""
    oos = wf.get("oos") or {}
    pf = wf.get("portfolio") or {}
    oos_ic = oos.get("mean_ic")
    excess = pf.get("excess")
    folds = [f for f in (wf.get("folds") or []) if f.get("ic") is not None]
    fold_stable = (not folds) or (sum(1 for f in folds if f["ic"] > 0) * 2 >= len(folds))
    evidence = (oos_ic is not None and oos_ic > 0
                and (excess is None or excess > 0) and fold_stable)
    n = len(rows)
    for r in rows:
        score = r.get("score")
        rank = r.get("rank") or 1
        cov = r.get("coverage") or 0.0
        pct_rank = 1.0 - (rank - 1) / float(max(1, n - 1))
        label, reason = "观察", "得分中性"
        if score is None or cov < 0.5:
            label, reason = "数据不足", "因子覆盖不足"
        elif evidence and score >= 95 and pct_rank >= 0.95:
            label, reason = "强候选", "得分前5% + 样本外正向"
        elif evidence and score >= 85 and pct_rank >= 0.85:
            label, reason = "候选", "得分前15% + 样本外正向"
        elif (not evidence) and score >= 90 and pct_rank >= 0.90:
            label, reason = "谨慎候选", "得分靠前，但样本外证据不足"
        elif score >= 60:
            label, reason = "观察", "得分中性偏强"
        else:
            label, reason = "回避", "得分偏低"
        vol = r.get("vol20")
        if vol is not None and vol > vol_cap:
            if label == "强候选":
                label = "候选"
                reason += "；20日波动偏高"
            elif label == "候选":
                label = "观察"
                reason += "；20日波动偏高"
            elif label == "谨慎候选":
                reason += "；20日波动偏高"
        pct = r.get("pct")
        if pct is not None and pct >= 7:
            reason += "；当日涨幅偏高"
        r["advice"] = label
        r["advice_reason"] = reason
        r["evidence"] = "正向" if evidence else "不足"
    return rows


def _empty_factor_row(key):
    return {
        "key": key, "label": FACTOR_DEFS[key][0],
        "category": FACTOR_DEFS[key][1],
        "category_label": CATEGORY_LABEL[FACTOR_DEFS[key][1]],
        "mean_ic": None, "icir": None, "t": None, "coverage": 0.0,
        "recent_ic": None, "win_rate": None, "ew_icir": None,
        "sign": 0, "weight": 0.0, "status": "无数据", "n_dates": 0,
    }


def run_factor_screen(limit=300, lookback=250, horizon=1, bars_n=320,
                      exclude_st=True, exclude_limit_up=True, threshold=None,
                      entry_lag=1, return_mode="open_to_close", workers=4,
                      use_cache=True, market="a", progress_cb=None,
                      cancel_event=None):
    t0 = time.time()
    if market == "crypto":
        _emit(progress_cb, "universe", 0, 1, "抓取加密成交额池...")
        universe = fetch_crypto_universe(limit)
        exclude_limit_up = False
    elif market == "etf":
        _emit(progress_cb, "universe", 0, 1, "抓取 ETF 成交额池...")
        universe = fetch_sina_universe(limit, exclude_st=False,
                                       node="etf_hq_fund", market="etf")
    elif market == "us":
        _emit(progress_cb, "universe", 0, 1, "抓取美股列表...")
        try:
            universe = fetch_us_universe(limit)
        except Exception:
            universe = []
        if not universe:
            universe = [{"symbol": "us" + x, "code": x, "name": x,
                         "price": None, "pct": None, "amount": 0,
                         "turnover": None, "market": "us"}
                        for x in US_FALLBACK[:limit]]
        exclude_limit_up = False
    elif market == "all":
        _emit(progress_cb, "universe", 0, 1, "抓取个股+ETF成交额池...")
        a_rows = fetch_sina_universe(limit, exclude_st, market="a")
        e_rows = fetch_sina_universe(limit, exclude_st=False,
                                     node="etf_hq_fund", market="etf")
        universe = sorted(a_rows + e_rows,
                          key=lambda r: r.get("amount") or 0, reverse=True)[:limit]
    else:
        _emit(progress_cb, "universe", 0, 1, "抓取成交额股票池...")
        universe = fetch_sina_universe(limit, exclude_st, market="a")
    if not universe:
        raise RuntimeError("池为空: 数据接口失败或被限流")
    symbols = [u["symbol"] for u in universe]
    _check(cancel_event)

    cache = _load_cache() if use_cache else {"bars": {}, "miss": {}}
    _emit(progress_cb, "bars", 0, len(symbols), "抓取日K...")
    bars_by_symbol, cache_hits, sources = fetch_universe_bars(
        symbols, n=bars_n, cache=cache, workers=workers,
        progress_cb=progress_cb, cancel_event=cancel_event, market=market)
    if use_cache:
        _save_cache(cache)
    if len(bars_by_symbol) < 20:
        raise RuntimeError(f"可用日K不足({len(bars_by_symbol)}只), 请稍后重试")
    _check(cancel_event)

    _emit(progress_cb, "panel", 0, 1, "抓取指数并构建因子面板...")
    if market == "crypto":
        index_bars = fetch_crypto_bars("BTCUSDT", bars_n)
    elif market == "us":
        index_bars = fetch_us_index_bars(bars_n)
    else:
        index_bars = fetch_index_bars(bars_n)
    panel = build_panel(bars_by_symbol, index_bars, lookback=lookback,
                        horizon=horizon, entry_lag=entry_lag,
                        return_mode=return_mode, progress_cb=progress_cb,
                        cancel_event=cancel_event)
    _check(cancel_event)

    _emit(progress_cb, "ic", 0, 1, "构建横截面排名...")
    build_rank_panel(panel, progress_cb=progress_cb, cancel_event=cancel_event)
    _emit(progress_cb, "ic", 0, 1, "计算 RankIC...")
    stats, ic_dates = compute_ic(panel, date_indices=list(range(len(panel.dates))),
                                 min_names=20, horizon=horizon)
    if not ic_dates:
        raise RuntimeError("没有足够的有效前瞻收益, 无法计算 IC")
    all_stats = summarize_ic(stats, len(ic_dates), len(panel.symbols))
    vol_analysis = analyze_volume(panel, horizon=horizon)

    wf = walk_forward(panel, stats, ic_dates, top_k=20, horizon=horizon,
                      exclude_limit=exclude_limit_up)
    live_weights, live_meta = select_weights(
        panel, all_stats, ic_dates, sign_map=wf.get("sign_map"))
    stocks = score_latest(panel, live_weights, universe, threshold=threshold,
                          exclude_limit_up=exclude_limit_up)
    stocks = annotate_advice(stocks, wf,
                             vol_cap=1.5 if market == "crypto" else 0.8)
    market_by_symbol = {u.get("symbol"): u.get("market", market) for u in universe}
    for r in stocks:
        r["market"] = market_by_symbol.get(r.get("symbol"), market)
    n_strong = sum(1 for r in stocks if r.get("advice") == "强候选")
    n_buy = sum(1 for r in stocks if r.get("advice") in ("强候选", "候选"))
    n_caution = sum(1 for r in stocks if r.get("advice") == "谨慎候选")

    factor_rows = []
    for key in FACTOR_KEYS:
        st = all_stats.get(key)
        if st is None or st["mean_ic"] is None:
            factor_rows.append(_empty_factor_row(key))
            continue
        lm = live_meta.get(key, {})
        w = lm.get("weight", 0.0)
        status = "入选" if w else lm.get("reason", "未入选")
        factor_rows.append({
            "key": key, "label": FACTOR_DEFS[key][0],
            "category": FACTOR_DEFS[key][1],
            "category_label": CATEGORY_LABEL[FACTOR_DEFS[key][1]],
            "mean_ic": st["mean_ic"], "icir": st["icir"], "t": st["t"],
            "coverage": st["coverage"],
            "recent_ic": st.get("recent_mean_ic"),
            "win_rate": st.get("win_rate"),
            "ew_icir": st.get("ew_icir"),
            "sign": 1 if ((st.get("ew_mean_ic") if st.get("ew_mean_ic") is not None
                           else st["mean_ic"]) > 0) else -1,
            "weight": w, "status": status, "n_dates": st["n_dates"],
        })
    factor_rows.sort(key=lambda r: (abs(r["weight"]), abs(r["mean_ic"] or 0)),
                     reverse=True)

    warnings = []
    if wf.get("oos", {}).get("mean_ic") is None:
        warnings.append("样本外检验不可用")
    elif wf["oos"]["mean_ic"] is not None and wf["oos"]["mean_ic"] <= 0:
        warnings.append("样本外RankIC不为正, 因子组合缺乏稳定证据")
    if len(panel.symbols) < 50:
        warnings.append("有效标的数较少, 横截面统计不稳定")
    if len(ic_dates) < 40:
        warnings.append(f"有效IC日期仅{len(ic_dates)}天, 因子选择易过拟合")
    if market != "crypto" and sources.get("sina"):
        warnings.append(f"{sources['sina']}只日K使用新浪不复权回退, 除权日附近因子可能失真")
    if sources.get("okx"):
        warnings.append(f"{sources['okx']}只加密日K使用OKX回退")
    if sources.get("nasdaq"):
        warnings.append(f"{sources['nasdaq']}只美股日K使用Nasdaq回退")
    pf = wf.get("portfolio") or {}
    if pf.get("excess") is not None and pf["excess"] <= 0:
        warnings.append("样本外Top20未跑赢等权基准, 买入标注已降级")
    if market == "crypto":
        warnings.append("加密日K为UTC日线, 当日未收盘bar不参与; 7x24交易无涨跌停")
    else:
        try:
            _today, _mins = _bj_now()
            if _mins < 15 * 60 + 10:
                warnings.append("盘中运行: 因子基于最近完整交易日, 收盘后信号更完整")
        except Exception:
            pass

    meta = {
        "market": market,
        "universe_label": {"a": "个股", "etf": "ETF", "crypto": "加密货币",
                           "us": "美股", "all": "个股+ETF"}.get(market, market),
        "n_universe": len(universe),
        "n_symbols": len(panel.symbols),
        "n_dates": len(panel.dates),
        "n_ic_dates": len(ic_dates),
        "n_candidates": len(stocks),
        "n_strong": n_strong,
        "n_buy": n_buy,
        "n_caution": n_caution,
        "evidence_ok": _evidence_ok(wf),
        "asof": stocks[0]["asof"] if stocks else (panel.dates[-1] if panel.dates else ""),
        "horizon": horizon,
        "entry_lag": entry_lag,
        "return_mode": return_mode,
        "selected": len([r for r in factor_rows if r["weight"]]),
        "cache_hits": cache_hits,
        "sources": sources,
        "elapsed": time.time() - t0,
        "warnings": warnings,
        "status": "OK" if live_weights else "无因子通过统计筛选",
        "volume_best": (vol_analysis.get("best") or {}).get("threshold"),
    }
    _emit(progress_cb, "done", 1, 1,
          f"完成: {len(stocks)} 只候选 · 入选因子 {meta['selected']} 个")
    return {
        "stocks": stocks,
        "factor_stats": factor_rows,
        "walk_forward": wf,
        "weights": live_weights,
        "volume_analysis": vol_analysis,
        "meta": meta,
    }


# ---------------------------------------------------------------------------
# 自检 / 命令行
# ---------------------------------------------------------------------------

def _synth_bars(n_symbols=80, n_days=320, seed=42):
    rnd = random.Random(seed)
    start = datetime.date(2025, 1, 2)
    dates = []
    d = start
    while len(dates) < n_days:
        if d.weekday() < 5:
            dates.append(d.isoformat())
        d += datetime.timedelta(days=1)

    market = []
    idx_bars = []
    idx_close = 3000.0
    for i, date in enumerate(dates):
        mret = 0.0002 + rnd.gauss(0, 0.008)
        market.append(mret)
        prev = idx_close
        idx_close = prev * (1 + mret)
        idx_bars.append((date, prev, idx_close, max(prev, idx_close) * 1.002,
                         min(prev, idx_close) * 0.998, 1e8))

    bars_by_symbol = {}
    for s in range(n_symbols):
        closes = [10.0 + rnd.random() * 30.0]
        rows = []
        for i in range(1, n_days):
            prev = closes[-1]
            past5 = (closes[-1] / closes[-6] - 1.0) if len(closes) >= 6 else 0.0
            intraday = 0.001 + 0.20 * past5 + market[i] + rnd.gauss(0, 0.018)
            intraday = max(-0.09, min(0.09, intraday))
            gap = max(-0.05, min(0.05, rnd.gauss(0, 0.004)))
            o = prev * (1 + gap)
            c = o * (1 + intraday)
            h = max(o, c) * (1 + abs(rnd.gauss(0, 0.004)))
            l = min(o, c) * (1 - abs(rnd.gauss(0, 0.004)))
            v = max(1000.0, 1e6 * (1 + abs(rnd.gauss(0, 0.35))))
            closes.append(c)
            rows.append((dates[i], o, c, h, l, v))
        sym = f"sh{600000 + s:06d}"
        bars_by_symbol[sym] = rows
    return bars_by_symbol, idx_bars


def _run_selftest():
    ok = True

    def check(name, cond):
        nonlocal ok
        print(("PASS " if cond else "FAIL ") + name)
        if not cond:
            ok = False

    check("Spearman monotonic", abs((_spearman(list(range(20)), list(range(20))) or 0) - 1) < 1e-9)
    check("percentile rank bounds", all(0 <= x <= 1 for x in _percentile_rank([1, 2, 3, 4])))

    bars_by_symbol, idx_bars = _synth_bars()
    idx_ret, idx_ret20 = _index_maps(idx_bars)
    sym = next(iter(bars_by_symbol))
    full = compute_symbol_factors(bars_by_symbol[sym], idx_ret, idx_ret20)
    cut_date = sorted(full)[150]
    cut_idx = next(i for i, b in enumerate(bars_by_symbol[sym]) if b[0] == cut_date)
    trunc = compute_symbol_factors(bars_by_symbol[sym][:cut_idx + 1], idx_ret, idx_ret20)
    check("truncation invariance", all(
        abs(full[cut_date][k] - trunc[cut_date][k]) < 1e-9
        for k in ("ret_5", "realvol_20", "rsi_14", "ma_dev_20")
        if k in full[cut_date] and k in trunc[cut_date]))

    panel = build_panel(bars_by_symbol, idx_bars, lookback=200, horizon=1)
    check("panel dimensions", len(panel.symbols) == len(bars_by_symbol) and len(panel.dates) == 200)
    stats, used = compute_ic(panel, date_indices=list(range(len(panel.dates))), horizon=1)
    check("IC dates", len(used) > 50)
    all_stats = summarize_ic(stats, len(used), len(panel.symbols))
    check("factor stats finite", sum(1 for s in all_stats.values()
                                     if s["mean_ic"] is not None) >= 20)
    wf = walk_forward(panel, stats, used)
    weights = wf.get("weights") or {}
    check("weights normalized", not weights or abs(sum(abs(w) for w in weights.values()) - 1) < 1e-6)
    check("OOS evaluated", wf.get("oos", {}).get("mean_ic") is not None)

    universe = [{"symbol": s, "code": s[2:], "name": s, "price": 10.0,
                 "pct": 1.0, "amount": 1e8, "turnover": 2.0}
                for s in panel.symbols]
    live_w, _meta = select_weights(panel, all_stats, used)
    stocks = score_latest(panel, live_w, universe, threshold=None)
    check("latest scores", bool(stocks) and all(0 <= r["score"] <= 100 for r in stocks))

    # 前瞻收益对齐: 信号日 t, t+1 开盘买入, t+1 收盘卖出
    simple = [("d0", 10.0, 10.0, 10.0, 10.0, 1.0),
              ("d1", 11.0, 12.0, 12.0, 10.5, 1.0),
              ("d2", 12.0, 13.0, 13.0, 11.0, 1.0)]
    simple_dates = ["d0", "d1", "d2"]
    fwd = _forward_return_dates({b[0]: b for b in simple}, simple_dates,
                                0, horizon=1, entry_lag=1)
    check("forward return alignment", abs((fwd or 0) - (12.0 / 11.0 - 1.0)) < 1e-12)

    print("SELFTEST", "OK" if ok else "FAILED")
    return ok


def _fmt_num(v, spec):
    return "--" if v is None else format(v, spec)


def _pct(v):
    return "--" if v is None else f"{v:+.2%}"


def _print_live(result):
    meta = result["meta"]
    wf = result["walk_forward"]
    print(f"{meta.get('universe_label', '池')} {meta['n_universe']} · 有效 {meta['n_symbols']} · "
          f"日期 {meta['n_dates']} · asof {meta['asof']} · "
          f"入选因子 {meta['selected']} · 用时 {meta['elapsed']:.1f}s")
    for w in meta.get("warnings") or []:
        print("WARN", w)
    print("\n因子 (按|权重|排序):")
    print(f"{'因子':<20}{'类别':<8}{'IC':>8}{'ICIR':>8}{'t':>8}{'覆盖':>7}"
          f"{'近20IC':>9}{'胜率':>6}{'权重':>9}  状态")
    for r in result["factor_stats"][:25]:
        recent = r.get("recent_ic")
        win = r.get("win_rate")
        print("%-20s%-8s%8s%8s%8s%6.0f%%%9s%5s%%%+8.1f%%  %s" % (
            r["label"], r["category_label"],
            _fmt_num(r["mean_ic"], "+.4f"),
            _fmt_num(r["icir"], "+.2f"),
            _fmt_num(r["t"], "+.1f"),
            r["coverage"] * 100,
            _fmt_num(recent, "+.4f"),
            "--" if win is None else "%.0f" % (win * 100),
            r["weight"] * 100, r["status"]))
    oos = wf.get("oos") or {}
    eq = wf.get("equal_oos") or {}
    print(f"\n样本外 RankIC {_fmt_num(oos.get('mean_ic'), '+.4f')} · "
          f"等权基准 {_fmt_num(eq.get('mean_ic'), '+.4f')} "
          f"· 训练/测试日期 {wf.get('train_dates')}/{wf.get('test_dates')}")
    print(f"\n次日研究标注: 强候选 {meta.get('n_strong', 0)} · "
          f"候选 {meta.get('n_buy', 0) - meta.get('n_strong', 0)} · "
          f"谨慎候选 {meta.get('n_caution', 0)} · "
          f"样本外证据 {'正向' if meta.get('evidence_ok') else '不足'}")
    print("\n筛选结果 (前20):")
    print(f"{'排名':>4} {'代码':<8}{'名称':<12}{'涨跌幅':>8}{'得分':>7}{'建议':<9}  主要贡献")
    for r in result["stocks"][:20]:
        pct_text = "--" if r["pct"] is None else f"{r['pct']:+.2f}%"
        print(f"{r['rank']:>4} {r['code']:<8}{r['name'][:10]:<12}"
              f"{pct_text:>8}{r['score']:>7.1f} {r.get('advice', ''):<9}  {r['top']}")
    pf = wf.get("portfolio") or {}
    if pf.get("n_dates"):
        print(f"\n样本外Top{pf['top_k']}组合(计{pf.get('cost', 0) * 100:.2f}%往返成本, 剔除涨停): "
              f"累计 {pf['cum']:+.2%} · "
              f"基准 {pf['bench_cum']:+.2%} · 超额 {pf['excess']:+.2%} · "
              f"年化 {_pct(pf['ann'])} · 夏普 {_fmt_num(pf['sharpe'], '.2f')} · "
              f"最大回撤 {pf['mdd']:+.2%} · 胜率 {pf['hit']:.0%} · {pf['n_dates']}期")
    print("\n历史IC使用的是今日成交额股票池, 存在选择/幸存者偏差; 仅供研究, 不构成投资建议。")


def main():
    try:
        sys.stdout.reconfigure(encoding="utf-8")
    except Exception:
        pass
    p = argparse.ArgumentParser(description="零依赖多因子选股引擎")
    p.add_argument("--selftest", action="store_true", help="离线自检")
    p.add_argument("--market", default="stock",
                   choices=("stock", "etf", "crypto", "us", "all"), help="市场")
    p.add_argument("--limit", type=int, default=300, help="池大小")
    p.add_argument("--lookback", type=int, default=250, help="因子回看交易日")
    p.add_argument("--bars", type=int, default=320, help="抓取日K根数")
    p.add_argument("--horizon", type=int, default=1, choices=(1, 5), help="前瞻收益天数")
    p.add_argument("--threshold", type=float, default=None, help="最低因子得分")
    p.add_argument("--workers", type=int, default=4, help="并发抓取数")
    p.add_argument("--include-st", action="store_true", help="包含ST/退市整理")
    p.add_argument("--include-limit", action="store_true", help="包含当前涨停股")
    p.add_argument("--no-cache", action="store_true", help="不使用磁盘缓存")
    args = p.parse_args()

    if args.selftest:
        raise SystemExit(0 if _run_selftest() else 1)

    result = run_factor_screen(
        limit=max(20, args.limit), lookback=max(80, args.lookback),
        horizon=args.horizon, bars_n=max(120, args.bars),
        exclude_st=not args.include_st,
        exclude_limit_up=not args.include_limit,
        threshold=args.threshold,
        market={"stock": "a", "etf": "etf", "crypto": "crypto",
                "us": "us", "all": "all"}.get(args.market, "a"),
        workers=max(1, args.workers), use_cache=not args.no_cache,
        progress_cb=lambda stage, done, total, msg:
            print(f"[{stage}] {msg}", flush=True))
    _print_live(result)


if __name__ == "__main__":
    main()