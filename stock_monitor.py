#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
A股 / 港股 / 美股 桌面看盘 + A股选股器 (零依赖: Python 标准库 + Tkinter)

数据源:
  - 自选股 / 指数: 腾讯财经 qt.gtimg.cn        (前缀 us / sh / sz / bj / hk)
  - 选股器:        新浪 A股全市场列表 (涨跌幅+换手率) + 腾讯单只补齐量比
  - 历史日K:       腾讯 web.ifzq.gtimg.cn (昨日涨幅对比 / 连涨 / 昨日量能)
  - 24h消息面:     东财个股资讯(np-listapi, 三市场) + 新浪 7x24 全球快讯
均为免费、免密钥、大陆可直连。行情为延时行情(美股/港股约15分钟, A股盘中约3秒), 仅供监控参考,
不构成任何投资建议。

运行:  python stock_monitor.py
"""

import json
import math
import os
import queue
import threading
import time
import urllib.request
import webbrowser
from concurrent.futures import ThreadPoolExecutor

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

MARKET_LABEL = {"us": "美股", "sh": "沪A", "sz": "深A", "bj": "北A", "hk": "港股"}

UA = {"User-Agent": "Mozilla/5.0 (Windows NT 10.0; Win64; x64)"}
SINA_HDR = {"User-Agent": UA["User-Agent"], "Referer": "https://finance.sina.com.cn/"}
SINA_LIST_URL = ("https://vip.stock.finance.sina.com.cn/quotes_service/api/json_v2.php/"
                 "Market_Center.getHQNodeData?page={page}&num={num}&sort=changepercent&asc=0&node=hs_a&symbol=")
EM_UT = "bd1d9ddb04089700cf9c27f6f7426281"
EM_HDR = {"User-Agent": UA["User-Agent"], "Referer": "https://quote.eastmoney.com/"}

# 涨跌配色(默认红涨绿跌, 界面可切换)
COLOR_UP_DEFAULT = "#d64545"
COLOR_DOWN_DEFAULT = "#2e9e5b"
COLOR_FLAT = "#666666"


# ---------------------------------------------------------------------------
# 基础工具
# ---------------------------------------------------------------------------

def _http(url, headers, timeout=8):
    req = urllib.request.Request(url, headers=headers)
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


def fmt_price(v):
    return "--" if v is None else f"{v:,.2f}"


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
    # 纯数字
    if s.isdigit():
        if len(s) == 5:
            return "hk" + s, s, "hk"          # 港股 5 位
        if len(s) == 6:
            c = s[0]
            if c in "69":
                return "sh" + s, s, "sh"      # 沪市
            if c in "023":
                return "sz" + s, s, "sz"      # 深市
            if c in "48":
                return "bj" + s, s, "bj"      # 北交所
            return "sz" + s, s, "sz"
    # 字母(可含 . 或 -) -> 美股
    return "us" + s, s, "us"


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
KLINE_HDR = {"User-Agent": UA["User-Agent"], "Referer": "https://gu.qq.com/"}

_KLINE_CACHE = {}       # symbol -> 昨日指标 dict(当日有效)
_KLINE_CACHE_FILE = os.path.join(os.path.dirname(os.path.abspath(__file__)), "kline_cache.json")
_KLINE_FAIL_TS = {}     # symbol -> 上次失败时间(负缓存, 避免反复重试打爆接口)
_KLINE_FAIL_TTL = 600.0


def _kline_today_ref(mkt):
    """判定日K最后一根是否为「当日」bar 的参照日期。
    美股交易日比北京日期晚约1天(收盘在北京凌晨), 以本地日期-36h 作参照。"""
    if mkt == "us":
        return time.strftime("%Y-%m-%d", time.localtime(time.time() - 36 * 3600))
    return time.strftime("%Y-%m-%d")


def fetch_daily_kline(symbol, n=12):
    """腾讯日K(前复权): 返回 list[dict(date,open,close,high,low,volume)] 旧->新, 失败返回 []。
    A股/港股直接用 sh/sz/bj/hk 前缀代码; 美股需带交易所后缀(如 usAAPL.OQ)。"""
    try:
        raw = _http(KLINE_URL.format(sym=symbol, n=n), KLINE_HDR, timeout=8).decode("utf-8", "replace")
        node = (json.loads(raw).get("data") or {}).get(symbol) or {}
        arr = node.get("qfqday") or node.get("day") or []
        out = []
        for b in arr:
            if isinstance(b, (list, tuple)) and len(b) >= 6:
                out.append({"date": str(b[0]), "open": to_float(b[1]), "close": to_float(b[2]),
                            "high": to_float(b[3]), "low": to_float(b[4]), "volume": to_float(b[5], 0)})
        return out
    except Exception:
        return []


def derive_prev_metrics(bars, today_ref):
    """从日K(旧->新)提取「昨日」截面指标(当日未定型 bar 不参与):
    p=昨日涨幅%  s=截至昨日连涨天数  vr=昨日量/前5日均量。数据不足返回 None。"""
    hist = [b for b in bars if b.get("close")]
    if hist and hist[-1]["date"][:10] == today_ref:
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
    m = derive_prev_metrics(fetch_daily_kline(symbol), _kline_today_ref(symbol[:2]))
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
#   3) 标签用固定阈值(65/35), 对应约前 1/3「高开」/ 后 1/3「低开」
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

# 开盘倾向标签阈值(0~100 分)
BIAS_HIGH = 65
BIAS_LOW = 35


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
    """详情页: 美股雪球, A股/港股腾讯。"""
    if mkt == "us":
        return f"https://xueqiu.com/S/{disp}"
    if mkt == "hk":
        return f"https://gu.qq.com/hk{disp}"
    return f"https://gu.qq.com/{mkt}{disp}"   # sh / sz / bj


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
)
NEWS_POSITIVE = (
    "回购", "增持", "中标", "签约", "预增", "扭亏", "分红", "派息", "股权激励",
    "收购", "重组", "涨价", "获批", "战略合作", "签订", "突破", "超预期", "新高", "强劲",
)

_ANNOUNCE_CACHE = {}
_ANNOUNCE_TTL = 300.0   # 公告静态, 缓存 5 分钟

# 自选盯盘表可点击排序的数值列
WATCH_NUMERIC_COLS = ("price", "change", "pct", "pct_prev", "delta", "open", "high", "low",
                      "prev", "volume")


def classify_announcement(title):
    """按公告标题关键词标注影响: 利好 / 利空 / 中性。启发式, 仅作参考。"""
    t = title or ""
    for kw in NEWS_NEGATIVE:
        if kw in t:
            return "利空"
    for kw in NEWS_POSITIVE:
        if kw in t:
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
# 主窗口
# ---------------------------------------------------------------------------

class StockMonitorApp:
    def __init__(self, root):
        self.root = root
        root.title("A股·港股·美股 行情监控 + 选股器 (延时行情)")
        root.geometry("1420x760")

        self._stop = False
        self._queue = queue.Queue()
        self._refresh_event = threading.Event()
        self._lock = threading.Lock()
        self._screen_busy = False

        self.watchlist = []
        self.index_results = {}
        self.stock_results = {}      # symbol -> (data, market)
        self.last_update = ""
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

        self._load_config()
        self._build_ui()
        self._start_worker()
        root.protocol("WM_DELETE_WINDOW", self._on_close)

    # ---------------- 配置 ----------------
    def _load_config(self):
        try:
            with open(CONFIG_FILE, "r", encoding="utf-8") as f:
                cfg = json.load(f)
            self.watchlist = [str(t).upper() for t in cfg.get("watchlist", DEFAULT_WATCHLIST)]
            self.interval = int(cfg.get("interval", 5))
            self.cn_color = bool(cfg.get("cn_color", True))
        except Exception:
            self.watchlist = list(DEFAULT_WATCHLIST)
            self.interval = 5
            self.cn_color = True
        self.interval = max(3, min(3600, self.interval))

    def _save_config(self):
        try:
            with open(CONFIG_FILE, "w", encoding="utf-8") as f:
                json.dump({"watchlist": self.watchlist, "interval": self.interval,
                           "cn_color": self.cn_color}, f, ensure_ascii=False, indent=2)
        except Exception as e:
            print("配置保存失败:", e)

    def _up_color(self):
        if self.cn_color:
            return COLOR_UP_DEFAULT, COLOR_DOWN_DEFAULT
        return COLOR_DOWN_DEFAULT, COLOR_UP_DEFAULT

    # ---------------- UI 骨架 ----------------
    def _build_ui(self):
        style = ttk.Style()
        style.theme_use("clam")
        nb = ttk.Notebook(self.root)
        nb.pack(fill="both", expand=True)
        self.tab_watch = ttk.Frame(nb)
        self.tab_screen = ttk.Frame(nb)
        self.tab_feed = ttk.Frame(nb)
        nb.add(self.tab_watch, text="  自选盯盘  ")
        nb.add(self.tab_screen, text="  选股器(A股)  ")
        nb.add(self.tab_feed, text="  7x24快讯  ")
        self._build_watch_tab()
        self._build_screen_tab()
        self._build_feed_tab()

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
        ttk.Button(ctrl, text="添加", command=self._add_symbols).pack(side="left", padx=2)
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
            self._refresh_event.wait(timeout=self.interval)
            self._refresh_event.clear()

    def _fetch_all(self):
        with self._lock:
            syms = list(self.watchlist)

        def get_symbol(sym):
            c = classify_symbol(sym)
            if not c:
                return sym, None, None
            tcode, disp, mkt = c
            try:
                raw = _http("https://qt.gtimg.cn/q=" + tcode, UA).decode("gbk", "replace")
                data = parse_tencent(raw)
                # 昨日对比指标(带当日缓存); 美股日K需带交易所后缀(如 usAAPL.OQ)
                ksym = ("us" + data["qt_code"]) if (mkt == "us" and data.get("qt_code")) else tcode
                m = fetch_prev_metrics(ksym)
                if m and m.get("p") is not None and data.get("pct") is not None:
                    data["pct_prev"] = m["p"]
                    data["delta"] = round(data["pct"] - m["p"], 2)
                return sym, data, mkt
            except Exception:
                return sym, None, mkt

        def get_index(tcode):
            try:
                raw = _http("https://qt.gtimg.cn/q=" + tcode, UA).decode("gbk", "replace")
                return parse_tencent(raw)
            except Exception:
                return None

        stocks = {}
        idx_list = []
        with ThreadPoolExecutor(max_workers=10) as ex:
            for sym, data, mkt in ex.map(get_symbol, syms):
                if data is not None:
                    stocks[sym] = (data, mkt)
            idx_list = list(ex.map(get_index, [ix[1] for ix in INDEXES]))
        indexes = {INDEXES[i][0]: idx_list[i] for i in range(len(INDEXES)) if idx_list[i]}
        return {"stocks": stocks, "indexes": indexes}

    def _poll(self):
        try:
            while True:
                res = self._queue.get_nowait()
                self.stock_results = res.get("stocks", {})
                self.index_results = res.get("indexes", {})
                self.last_update = res.get("ts", "")
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
            vals = (
                MARKET_LABEL.get(mkt, "?"),
                sym,
                d.get("name") or "",
                fmt_price(d.get("price")),
                fmt_signed(d.get("change")),
                fmt_pct(d.get("pct")),
                fmt_pct(d.get("pct_prev")),
                fmt_pct(d.get("delta")),
                fmt_price(d.get("open")),
                fmt_price(d.get("high")),
                fmt_price(d.get("low")),
                fmt_price(d.get("prev_close")),
                fmt_vol(d.get("volume")),
                d.get("time") or "",
            )
            self.tree.insert("", "end", values=vals, tags=(tag,))
        n = len(syms)
        ok = len(self.stock_results)
        self.status_var.set(
            f"数据源: 腾讯(延时) · 最后刷新 {self.last_update} · 共 {n} 只 · 正常 {ok} · "
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
        top = ttk.Frame(self.tab_screen, padding=(8, 6))
        top.pack(fill="x")

        ttk.Label(top, text="A股全市场选股", font=("Microsoft YaHei", 11, "bold")).pack(side="left")

        ttk.Label(top, text="  涨幅").pack(side="left")
        self.f_min_var = tk.StringVar(value="4.0")
        ttk.Entry(top, textvariable=self.f_min_var, width=5).pack(side="left")
        ttk.Label(top, text="% ~ ").pack(side="left")
        self.f_max_var = tk.StringVar(value="5.0")
        ttk.Entry(top, textvariable=self.f_max_var, width=5).pack(side="left")
        ttk.Label(top, text="%").pack(side="left")

        ttk.Label(top, text="   量比≥").pack(side="left")
        self.f_lb_var = tk.StringVar(value="1.5")
        ttk.Entry(top, textvariable=self.f_lb_var, width=5).pack(side="left")

        ttk.Label(top, text="  换手率≥").pack(side="left")
        self.f_hs_var = tk.StringVar(value="3.0")
        ttk.Entry(top, textvariable=self.f_hs_var, width=5).pack(side="left")
        ttk.Label(top, text="%").pack(side="left")

        ttk.Label(top, text="  排序:").pack(side="left")
        self.sort_var = tk.StringVar(value="量比")
        ttk.Combobox(top, textvariable=self.sort_var, width=8, state="readonly",
                     values=("量比", "换手率", "涨跌幅", "昨涨幅", "涨幅差", "连涨",
                             "24h消息", "成交额", "开盘倾向")).pack(side="left", padx=2)

        self.screen_btn = ttk.Button(top, text="查询", command=self._run_screen)
        self.screen_btn.pack(side="left", padx=6)

        self.screen_count_var = tk.StringVar(value="点击「查询」开始筛选")
        ttk.Label(top, textvariable=self.screen_count_var, foreground="#333").pack(side="left", padx=10)

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
        ttk.Label(top2, text="· 留空/不勾 = 不限", foreground="#888").pack(side="left", padx=6)

        # 结果表格
        cols = ("code", "name", "industry", "price", "pct", "pct_prev", "delta", "streak",
                "news", "lb", "hs", "amount", "volume", "bias")
        headers = ("代码", "名称", "行业", "现价", "涨跌幅", "昨涨幅", "涨幅差", "连涨",
                   "24h消息", "量比", "换手率", "成交额", "成交量", "开盘倾向")
        widths = (72, 100, 88, 76, 76, 72, 72, 48, 104, 60, 72, 88, 88, 92)
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
            lb_min = float(self.f_lb_var.get())
            hs_min = float(self.f_hs_var.get())
            p_min = opt_float(self.f_prev_min_var)
            p_max = opt_float(self.f_prev_max_var)
            st_min = opt_float(self.f_streak_var)
        except ValueError:
            messagebox.showwarning("参数错误", "请填写数字: 涨幅区间 / 量比 / 换手率 / 昨日涨幅 / 连涨")
            return
        if f_min > f_max:
            f_min, f_max = f_max, f_min
        if p_min is not None and p_max is not None and p_min > p_max:
            p_min, p_max = p_max, p_min
        if st_min is not None:
            st_min = max(0, st_min)
        accel_only = self.f_accel_var.get()
        news_only = self.f_news_var.get()

        self._screen_busy = True
        self.screen_btn.configure(state="disabled")
        self.screen_count_var.set("筛选中, 请稍候...")

        def work():
            try:
                self.root.after(0, lambda: self.screen_count_var.set("正在抓取 A股行情..."))
                raw = sina_fetch_candidates(f_min)
                # 第一段: 用新浪字段过滤 涨幅区间 + 换手率
                cands = []
                for r in raw:
                    cp = to_float(r.get("changepercent"))
                    if cp is None or not (f_min <= cp <= f_max):
                        continue
                    hs = to_float(r.get("turnoverratio")) or 0.0
                    if hs < hs_min:
                        continue
                    cands.append(r)
                # 第二段: 腾讯单只补齐量比(带 TTL 缓存)
                self.root.after(0, lambda: self.screen_count_var.set(f"正在计算量比... ({len(cands)} 只)"))
                def enrich(r):
                    lb, _hs = fetch_a_metrics(r.get("symbol"))
                    r["lb"] = lb
                    return r
                if cands:
                    with ThreadPoolExecutor(max_workers=24) as ex:
                        cands = list(ex.map(enrich, cands))
                # 第三段: 日K补齐「昨日」指标(昨涨幅/连涨/昨日量比, 当日缓存), 供对比过滤与打分
                self.root.after(0, lambda: self.screen_count_var.set(
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
                self.root.after(0, lambda: self.screen_count_var.set(
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
                    cp = to_float(r.get("changepercent"))
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
                        "price": to_float(r.get("trade")),
                        "pct": cp,
                        "pct_prev": pp,
                        "delta": delta,
                        "streak": streak,
                        "vr": r.get("vr"),
                        "news_pos": n_pos,
                        "news_neg": n_neg,
                        "news_score": n_pos - n_neg,
                        "lb": lb,
                        "hs": to_float(r.get("turnoverratio")),
                        "amount": to_float(r.get("amount"), 0),
                        "volume": to_float(r.get("volume"), 0),
                        "high": to_float(r.get("high")),
                        "low": to_float(r.get("low")),
                        "industry": "…",
                    })
                # 横截面多因子合成开盘倾向(分位排名 + 加权, 0~100)
                open_bias_composite(rows)
                sort_key = {"量比": "lb", "换手率": "hs", "涨跌幅": "pct", "昨涨幅": "pct_prev",
                            "涨幅差": "delta", "连涨": "streak", "24h消息": "news_score",
                            "成交额": "amount", "开盘倾向": "bias"}
                key = sort_key.get(self.sort_var.get(), "lb")
                rows.sort(key=lambda x: x.get(key) if x.get(key) is not None else -1e18, reverse=True)
                # 先显示(行业占位为 …)
                self.root.after(0, lambda: self._deliver(rows, final=False))
                # 第三段: 补齐行业(带缓存), 完成后更新
                if rows:
                    def add_industry(row):
                        row["industry"] = fetch_industry(row.get("symbol"))
                        return row
                    with ThreadPoolExecutor(max_workers=16) as ex:
                        rows = list(ex.map(add_industry, rows))
                self.root.after(0, lambda: self._deliver(rows, final=True))
            except Exception as e:
                self.root.after(0, lambda: self._deliver([], final=True))
                self.root.after(0, lambda: self.screen_count_var.set(f"查询失败: {e}"))

        threading.Thread(target=work, daemon=True).start()

    def _deliver(self, rows, final):
        self.screen_rows = rows
        if self.screen_sort_col:
            self._apply_screen_sort()
        self.screen_page = 0
        self._render_screen_table()
        if final:
            self._screen_busy = False
            self.screen_btn.configure(state="normal")
            self.screen_count_var.set(f"共筛出 {len(rows)} 只 (涨幅区间 + 换手 + 量比 + 昨日对比 + 24h消息面)")
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
            tag = "up" if label == "高开" else ("down" if label == "低开" else "flat")
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
            )
            self.stree.insert("", "end", values=vals, tags=(tag,))
        self.page_var.set(f"第 {self.screen_page + 1} / {pages} 页")

    def _screen_sort_value(self, r, col):
        """选股器行某列的可排序值; None 表示缺失(排最后)。"""
        if col == "news":
            return r.get("news_score")
        if col in ("price", "pct", "pct_prev", "delta", "streak", "lb", "hs", "amount",
                   "volume", "bias"):
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
        menu = tk.Menu(self.root, tearoff=0)
        menu.add_command(label=f"复制代码 {code}", command=lambda: self._copy_code(code))
        c = classify_symbol(code)
        mkt = c[2] if c else ""
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
        win.title(f"公告消息 - {disp}")
        win.geometry("760x540")
        win.transient(self.root)

        hdr = ttk.Frame(win, padding=(8, 6))
        hdr.pack(fill="x")
        ttk.Label(hdr, text=f"{disp} 基本面公告 · 利好/利空为关键词启发式标注",
                  font=("Microsoft YaHei", 10, "bold")).pack(side="left")
        status = tk.StringVar(value="加载中...")
        ttk.Label(hdr, textvariable=status, foreground="#666").pack(side="right")

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
        win.title(f"24h消息面 - {disp}")
        win.geometry("880x560")
        win.transient(self.root)

        hdr = ttk.Frame(win, padding=(8, 6))
        hdr.pack(fill="x")
        ttk.Label(hdr, text=f"{disp} 近24小时资讯 · 利好/利空为关键词启发式标注",
                  font=("Microsoft YaHei", 10, "bold")).pack(side="left")
        status = tk.StringVar(value="加载中...")
        ttk.Label(hdr, textvariable=status, foreground="#666").pack(side="right")

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
        ttk.Label(ctrl, textvariable=self.feed_status_var, foreground="#666").pack(side="right")

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

    # ---------------- 关闭 ----------------
    def _on_close(self):
        self._stop = True
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
