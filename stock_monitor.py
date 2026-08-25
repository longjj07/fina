#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
A股 / 港股 / 美股 桌面看盘 + A股选股器 (零依赖: Python 标准库 + Tkinter)

数据源:
  - 自选股 / 指数: 腾讯财经 qt.gtimg.cn        (前缀 us / sh / sz / bj / hk)
  - 选股器:        新浪 A股全市场列表 (涨跌幅+换手率) + 腾讯单只补齐量比
均为免费、免密钥、大陆可直连。行情为延时行情(美股/港股约15分钟, A股盘中约3秒), 仅供监控参考,
不构成任何投资建议。

运行:  python stock_monitor.py
"""

import json
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


def open_bias_score(close, high, low, liangbi, pct, lo=4.0, hi=5.0):
    """次日开盘倾向: 返回 (分数, 标签)。分数 -100(低开) ~ +100(高开)。
    依据: 收盘位置(尾盘强弱)为主, 量比(动能)与涨幅区间位置为辅。"""
    try:
        close, high, low = float(close), float(high), float(low)
    except (TypeError, ValueError):
        return 0, "中性"
    rng = high - low
    pos = (close - low) / rng if rng > 0 else 0.5
    s1 = (pos - 0.5) * 80
    lb = float(liangbi) if liangbi is not None else 1.0
    s2 = max(-15, min(15, (lb - 1.0) * 12))
    frac = (pct - lo) / (hi - lo) if (pct is not None and hi > lo) else 0.5
    s3 = (frac - 0.5) * 20
    score = max(-100, min(100, round(s1 + s2 + s3)))
    label = "高开" if score >= 15 else ("低开" if score <= -15 else "中性")
    return score, label


def detail_url(mkt, disp):
    """详情页: 美股雪球, A股/港股腾讯。"""
    if mkt == "us":
        return f"https://xueqiu.com/S/{disp}"
    if mkt == "hk":
        return f"https://gu.qq.com/hk{disp}"
    return f"https://gu.qq.com/{mkt}{disp}"   # sh / sz / bj


# ---------------------------------------------------------------------------
# 主窗口
# ---------------------------------------------------------------------------

class StockMonitorApp:
    def __init__(self, root):
        self.root = root
        root.title("A股·港股·美股 行情监控 + 选股器 (延时行情)")
        root.geometry("1280x720")

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
        nb.add(self.tab_watch, text="  自选盯盘  ")
        nb.add(self.tab_screen, text="  选股器(A股)  ")
        self._build_watch_tab()
        self._build_screen_tab()

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
        cols = ("mkt", "code", "name", "price", "change", "pct", "open", "high", "low",
                "prev", "volume", "time")
        headers = ("市场", "代码", "名称", "现价", "涨跌", "涨跌幅", "开盘", "最高", "最低",
                   "昨收", "成交量", "更新时间")
        widths = (52, 80, 120, 88, 88, 88, 88, 88, 88, 88, 96, 150)
        tf = ttk.Frame(self.tab_watch, padding=(8, 4))
        tf.pack(fill="both", expand=True)
        self.tree = ttk.Treeview(tf, columns=cols, show="headings")
        for c, h, w in zip(cols, headers, widths):
            self.tree.heading(c, text=h)
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
                return sym, parse_tencent(raw), mkt
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
                     values=("量比", "换手率", "涨跌幅", "成交额", "开盘倾向")).pack(side="left", padx=2)

        self.screen_btn = ttk.Button(top, text="查询", command=self._run_screen)
        self.screen_btn.pack(side="left", padx=6)

        self.screen_count_var = tk.StringVar(value="点击「查询」开始筛选")
        ttk.Label(top, textvariable=self.screen_count_var, foreground="#333").pack(side="left", padx=10)

        # 结果表格
        cols = ("code", "name", "industry", "price", "pct", "lb", "hs", "amount", "volume", "bias")
        headers = ("代码", "名称", "行业", "现价", "涨跌幅", "量比", "换手率", "成交额", "成交量", "开盘倾向")
        widths = (76, 108, 92, 84, 84, 66, 76, 92, 92, 96)
        tf = ttk.Frame(self.tab_screen, padding=(8, 4))
        tf.pack(fill="both", expand=True)
        self.stree = ttk.Treeview(tf, columns=cols, show="headings")
        for c, h, w in zip(cols, headers, widths):
            self.stree.heading(c, text=h)
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
        try:
            f_min = float(self.f_min_var.get())
            f_max = float(self.f_max_var.get())
            lb_min = float(self.f_lb_var.get())
            hs_min = float(self.f_hs_var.get())
        except ValueError:
            messagebox.showwarning("参数错误", "请填写数字: 涨幅区间 / 量比 / 换手率")
            return
        if f_min > f_max:
            f_min, f_max = f_max, f_min

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
                # 组装行 + 立即算开盘倾向(不需要行业), 先交付结果
                rows = []
                for r in cands:
                    lb = to_float(r.get("lb")) or 0.0
                    if lb < lb_min:
                        continue
                    pct = to_float(r.get("changepercent"))
                    score, label = open_bias_score(to_float(r.get("trade")),
                                                   to_float(r.get("high")),
                                                   to_float(r.get("low")),
                                                   to_float(r.get("lb")), pct, f_min, f_max)
                    rows.append({
                        "code": r.get("code"), "name": r.get("name"),
                        "symbol": r.get("symbol"),
                        "price": to_float(r.get("trade")),
                        "pct": pct,
                        "lb": to_float(r.get("lb")),
                        "hs": to_float(r.get("turnoverratio")),
                        "amount": to_float(r.get("amount"), 0),
                        "volume": to_float(r.get("volume"), 0),
                        "high": to_float(r.get("high")),
                        "low": to_float(r.get("low")),
                        "industry": "…",
                        "bias": score,
                        "bias_label": label,
                    })
                sort_key = {"量比": "lb", "换手率": "hs", "涨跌幅": "pct",
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
        self.screen_page = 0
        self._render_screen_table()
        if final:
            self._screen_busy = False
            self.screen_btn.configure(state="normal")
            self.screen_count_var.set(f"共筛出 {len(rows)} 只 (A股: 涨幅区间 + 换手率 + 量比)")
            _save_industry_cache()
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
            bias_text = "--" if score is None else f"{label} {score:+d}"
            vals = (
                r["code"],
                r["name"] or "",
                r.get("industry") or "—",
                fmt_price(r.get("price")),
                fmt_pct(r.get("pct")),
                fmt_price(r.get("lb")),
                fmt_pct_plain(r.get("hs")),
                fmt_amount(r.get("amount")),
                fmt_vol(r.get("volume")),
                bias_text,
            )
            self.stree.insert("", "end", values=vals, tags=(tag,))
        self.page_var.set(f"第 {self.screen_page + 1} / {pages} 页")

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

    # ---------------- 关闭 ----------------
    def _on_close(self):
        self._stop = True
        self._save_config()
        _save_industry_cache()
        self.root.destroy()


def main():
    _load_industry_cache()
    root = tk.Tk()
    app = StockMonitorApp(root)
    app._poll()
    root.mainloop()


if __name__ == "__main__":
    main()
