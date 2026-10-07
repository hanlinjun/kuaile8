# -*- coding: utf-8 -*-
"""
快乐8 · 超几何摇奖模拟器
核心：有限总体无放回抽样 → 超几何分布
N=80, K=20, 玩家选号 n∈[1,10], 命中数 X ~ Hypergeometric(N,K,n)
"""

from __future__ import annotations

import math
import os
import random
import re
import secrets
import sys
import time
import tkinter as tk
import urllib.error
import urllib.request
from collections import Counter, defaultdict
from tkinter import messagebox, ttk
from typing import Dict, List, Optional, Sequence, Tuple


def resource_path(name: str) -> str:
    """兼容开发与 PyInstaller 打包的资源路径。"""
    base = getattr(sys, "_MEIPASS", os.path.dirname(os.path.abspath(__file__)))
    return os.path.join(base, name)

# ── 游戏常量（快乐8）──────────────────────────────────────────
N_POOL = 80          # 总体号码数
K_DRAW = 20          # 每期开奖号数量
N_PICK_MIN = 1
N_PICK_MAX = 10
P_SINGLE = K_DRAW / N_POOL  # 理论单号出现频率 25%
KILL_POOL_MIN = 2      # 杀号后奖池最少保留号码数

# ── 2号模块：主号 6/33 + 副号 1/16 ────────────────────────────
M2_MAIN_POOL = 33
M2_MAIN_COUNT = 6
M2_SPECIAL_POOL = 16
M2_SPECIAL_COUNT = 1
M2_GROUP_MIN = 1
M2_GROUP_MAX = 50

# ── 主题色 ────────────────────────────────────────────────────
BG = "#0a0e1a"
CARD = "#141b2d"
INPUT = "#0d1220"
GOLD = "#f0c040"
GOLD_DIM = "#c9a020"
RED = "#e84545"
GREEN = "#2ecc71"
BLUE = "#4a9eff"
TEXT = "#eef2ff"
MUTED = "#8892b0"
BORDER = "#2a3350"
HIT = "#27ae60"
MISS = "#3d4a66"

BALL_PALETTE = [
    ("#ff6b6b", "#c0392b"),
    ("#5dade2", "#2e86c1"),
    ("#58d68d", "#27ae60"),
    ("#bb8fce", "#8e44ad"),
    ("#f5b041", "#d68910"),
]


# ══════════════════════════════════════════════════════════════
# 核心数学：超几何分布及其他配套算法
# ══════════════════════════════════════════════════════════════

def comb(n: int, k: int) -> int:
    if k < 0 or n < 0 or k > n:
        return 0
    return math.comb(n, k)


def hypergeometric_pmf(N: int, K: int, n: int, k: int) -> float:
    """
    P(X=k) = C(K,k) * C(N-K, n-k) / C(N, n)
    有限总体无放回抽样的精确命中概率（快乐8原生模型）。
    """
    if n < 0 or n > N or K < 0 or K > N:
        return 0.0
    if k < max(0, n - (N - K)) or k > min(n, K):
        return 0.0
    den = comb(N, n)
    if den == 0:
        return 0.0
    return comb(K, k) * comb(N - K, n - k) / den


def hypergeometric_table(N: int, K: int, n: int) -> List[Tuple[int, float]]:
    return [(k, hypergeometric_pmf(N, K, n, k)) for k in range(0, n + 1)]


def hypergeometric_mean(N: int, K: int, n: int) -> float:
    """E[X] = n * K / N"""
    return n * K / N if N else 0.0


KILL = "#8b2942"
KILL_FG = "#ffb4c0"


def draw_official(killed: Optional[Sequence[int]] = None) -> List[int]:
    """从 1..80 去掉杀号后，无放回抽取开奖号（奖池不足20个时全抽，至少保留2个）。"""
    killed_set = set(killed or [])
    pool = [i for i in range(1, N_POOL + 1) if i not in killed_set]
    if len(pool) < KILL_POOL_MIN:
        raise ValueError(f"可用号码不足 {KILL_POOL_MIN} 个（当前剩余 {len(pool)}），请减少杀号。")
    return sorted(random.sample(pool, min(K_DRAW, len(pool))))


# ══════════════════════════════════════════════════════════════
# 真随机引擎（2号模块专用）：禁止 MT19937 等伪随机
# 优先 RANDOM.ORG 大气噪声；备选操作系统密码学熵源 os.urandom
# ══════════════════════════════════════════════════════════════

class TrueRandomError(RuntimeError):
    pass


def _random_org_integers(count: int, min_v: int, max_v: int, timeout: float = 12.0) -> List[int]:
    """从 RANDOM.ORG 拉取真随机整数（大气噪声）。"""
    if count <= 0:
        return []
    if min_v > max_v:
        raise TrueRandomError("随机区间无效")
    # 官方 plain API 单次建议不要过大
    url = (
        "https://www.random.org/integers/"
        f"?num={count}&min={min_v}&max={max_v}&col=1&base=10&format=plain&rnd=new"
    )
    req = urllib.request.Request(url, headers={"User-Agent": "Happy8TrueRNG/1.0"})
    try:
        with urllib.request.urlopen(req, timeout=timeout) as resp:
            raw = resp.read().decode("utf-8", errors="replace").strip()
    except urllib.error.HTTPError as e:
        raise TrueRandomError(f"RANDOM.ORG HTTP {e.code}：配额不足或服务繁忙") from e
    except Exception as e:
        raise TrueRandomError(f"不会吧，不会吧！不会现在还有人断网吧！真可怜！要联网才能用") from e
    if not raw:
        raise TrueRandomError("RANDOM.ORG 返回空数据")
    try:
        vals = [int(x.strip()) for x in raw.splitlines() if x.strip()]
    except ValueError as e:
        raise TrueRandomError("RANDOM.ORG 返回无法解析") from e
    if len(vals) != count:
        raise TrueRandomError(f"RANDOM.ORG 数量不符：期望 {count}，得到 {len(vals)}")
    for v in vals:
        if v < min_v or v > max_v:
            raise TrueRandomError("RANDOM.ORG 返回越界数值")
    return vals


def _os_crypto_randbelow(n: int) -> int:
    """操作系统密码学安全熵源（os.urandom / secrets），非伪随机 MT。"""
    if n <= 0:
        raise TrueRandomError("randbelow 参数无效")
    return secrets.randbelow(n)


def true_randbelow(n: int, prefer_org: bool = True) -> Tuple[int, str]:
    """返回 (值, 熵源名称)。"""
    if prefer_org:
        try:
            return _random_org_integers(1, 0, n - 1)[0], "RANDOM.ORG"
        except TrueRandomError:
            pass
    return _os_crypto_randbelow(n), "OS-CSPRNG(os.urandom)"


def true_sample(population: Sequence[int], k: int, prefer_org: bool = True, allow_fallback: bool = True) -> Tuple[List[int], str]:
    """
    无放回真随机抽样（支持杀号后的非连续总体）。
    RANDOM.ORG：批量取数，只保留总体内号码；OS：Fisher–Yates + secrets.randbelow。
    绝不使用 Python random / MT19937 伪随机。
    """
    pool = list(population)
    n = len(pool)
    if k < 0 or k > n:
        raise TrueRandomError("抽样数量非法（可能因杀号过多导致奖池不足）")
    if k == 0:
        return [], "NONE"

    pool_set = set(pool)
    if prefer_org:
        try:
            lo, hi = min(pool), max(pool)
            chosen: List[int] = []
            seen = set()
            guard = 0
            while len(chosen) < k:
                guard += 1
                if guard > 40:
                    raise TrueRandomError("RANDOM.ORG 去重抽样重试过多")
                need = k - len(chosen)
                density = max(0.15, len(pool_set) / max(1, hi - lo + 1))
                batch_n = min(max(int(need * 3 / density), need), 100)
                batch = _random_org_integers(batch_n, lo, hi)
                for v in batch:
                    if v in pool_set and v not in seen:
                        seen.add(v)
                        chosen.append(v)
                        if len(chosen) == k:
                            break
            return sorted(chosen), "RANDOM.ORG"
        except TrueRandomError:
            if not allow_fallback:
                raise
            pool = list(population)

    for i in range(k):
        j = i + _os_crypto_randbelow(len(pool) - i)
        pool[i], pool[j] = pool[j], pool[i]
    return sorted(pool[:k]), "OS-CSPRNG(os.urandom)"


def true_draw_main_special(
    prefer_org: bool = True,
    allow_fallback: bool = True,
    kill_main: Optional[Sequence[int]] = None,
    kill_special: Optional[Sequence[int]] = None,
) -> Tuple[List[int], int, str]:
    """抽一组：主号6个(1-33) + 副号1个(1-16)，已杀号永不进入结果。"""
    kill_m = set(kill_main or [])
    kill_s = set(kill_special or [])
    main_pool = [i for i in range(1, M2_MAIN_POOL + 1) if i not in kill_m]
    special_pool = [i for i in range(1, M2_SPECIAL_POOL + 1) if i not in kill_s]
    if len(main_pool) < M2_MAIN_COUNT:
        raise TrueRandomError(
            f"主号可用不足 {M2_MAIN_COUNT} 个（剩余 {len(main_pool)}），请减少主号杀号。"
        )
    if len(special_pool) < M2_SPECIAL_COUNT:
        raise TrueRandomError(
            f"副号可用不足 {M2_SPECIAL_COUNT} 个（剩余 {len(special_pool)}），请减少副号杀号。"
        )
    mains, src1 = true_sample(
        main_pool, M2_MAIN_COUNT,
        prefer_org=prefer_org, allow_fallback=allow_fallback,
    )
    specials, src2 = true_sample(
        special_pool, M2_SPECIAL_COUNT,
        prefer_org=prefer_org, allow_fallback=allow_fallback,
    )
    src = src1 if src1 == src2 else f"{src1}+{src2}"
    return mains, specials[0], src


def format_ticket(mains: Sequence[int], special: int) -> str:
    """格式：xxxxxx+x（主号两位补零连写 + 副号两位）。"""
    body = "".join(f"{n:02d}" for n in mains)
    return f"{body}+{special:02d}"


def hit_count(picks: Sequence[int], drawn: Sequence[int]) -> int:
    return len(set(picks) & set(drawn))


def parity_stats(nums: Sequence[int]) -> Tuple[int, int]:
    odd = sum(1 for x in nums if x % 2 == 1)
    return odd, len(nums) - odd


def size_stats(nums: Sequence[int]) -> Tuple[int, int]:
    """小数 1-40 / 大号 41-80"""
    small = sum(1 for x in nums if x <= 40)
    return small, len(nums) - small


def zone_stats(nums: Sequence[int]) -> Tuple[int, int, int, int]:
    """四区：1-20 / 21-40 / 41-60 / 61-80"""
    z = [0, 0, 0, 0]
    for x in nums:
        z[(x - 1) // 20] += 1
    return tuple(z)  # type: ignore


def simulate_periods(periods: int) -> List[List[int]]:
    return [draw_official() for _ in range(periods)]


def frequency_map(history: Sequence[Sequence[int]]) -> Dict[int, int]:
    c: Counter = Counter()
    for draw in history:
        c.update(draw)
    return {i: c.get(i, 0) for i in range(1, N_POOL + 1)}


def missing_map(history: Sequence[Sequence[int]]) -> Dict[int, int]:
    """当前遗漏：距最近一次出现经过的期数。"""
    last = {i: -1 for i in range(1, N_POOL + 1)}
    for t, draw in enumerate(history):
        for x in draw:
            last[x] = t
    end = len(history) - 1
    return {i: (end - last[i]) if last[i] >= 0 else len(history) for i in range(1, N_POOL + 1)}


def apriori_pairs(history: Sequence[Sequence[int]], top_n: int = 12) -> List[Tuple[Tuple[int, int], int]]:
    """简易共现挖掘（Apriori 思想的二元频繁项）。"""
    pair_c: Counter = Counter()
    for draw in history:
        s = sorted(draw)
        for i in range(len(s)):
            for j in range(i + 1, len(s)):
                pair_c[(s[i], s[j])] += 1
    return pair_c.most_common(top_n)


def genetic_balanced_ticket(n: int, generations: int = 40, pop: int = 60) -> List[int]:
    """
    遗传算法选号优化（学术仿真）：
    约束奇偶≈均衡、大小≈均衡、四区分散。不能提高真实中奖概率。
    """
    def fitness(genes: List[int]) -> float:
        odd, even = parity_stats(genes)
        small, big = size_stats(genes)
        z = zone_stats(genes)
        # 目标：奇偶差、大小差尽可能小，区间方差小
        score = 0.0
        score -= abs(odd - even)
        score -= abs(small - big)
        mean_z = n / 4
        score -= sum((zi - mean_z) ** 2 for zi in z)
        return score

    def individual() -> List[int]:
        return sorted(random.sample(range(1, N_POOL + 1), n))

    population = [individual() for _ in range(pop)]
    for _ in range(generations):
        population.sort(key=fitness, reverse=True)
        elites = population[: pop // 5]
        children = elites[:]
        while len(children) < pop:
            a, b = random.sample(elites[: max(4, len(elites))], 2)
            pool = sorted(set(a) | set(b))
            if len(pool) < n:
                child = individual()
            else:
                child = sorted(random.sample(pool, n))
            # 变异
            if random.random() < 0.35:
                child = sorted(set(child))
                idx = random.randrange(n)
                cand = random.randint(1, N_POOL)
                while cand in child:
                    cand = random.randint(1, N_POOL)
                child[idx] = cand
                child = sorted(set(child))
                while len(child) < n:
                    x = random.randint(1, N_POOL)
                    if x not in child:
                        child.append(x)
                child = sorted(child)[:n]
            children.append(sorted(child))
        population = children
    population.sort(key=fitness, reverse=True)
    return population[0]


def bayesian_posteriors(history: Sequence[Sequence[int]], alpha: float = 1.0, beta: float = 3.0) -> Dict[int, float]:
    """
    贝叶斯更新（Beta-Binomial 直觉简化）：
    先验 ≈ 理论命中率 20/80；后验均值 = (α + hits) / (α+β + periods)
    仅复盘，不改变真实独立开奖概率。
    """
    periods = len(history)
    hits = frequency_map(history)
    # 先验均值 α/(α+β) ≈ 0.25 → α=1, β=3
    return {
        i: (alpha + hits[i]) / (alpha + beta + periods) if periods else alpha / (alpha + beta)
        for i in range(1, N_POOL + 1)
    }


def fmt_pct(p: float) -> str:
    return f"{p * 100:.4f}%"


# ══════════════════════════════════════════════════════════════
# 真实历史数据：500彩票网 快乐8 走势接口爬取 + 解析 + 统计推理
# 数据源：datachart.500.com/kl8/zoushi/newinc/jbzs_redblue.php
#   expect=30/50/100 → 精确返回对应期数；其它值 → 返回全部历史（约1700+期）
#   编码 gb2312；每期一行：期号 20xxxxx + 80 列，chartBall 单元格文本即开出号码
# ══════════════════════════════════════════════════════════════

KL8_HISTORY_URL = "https://datachart.500.com/kl8/zoushi/newinc/jbzs_redblue.php"
KL8_UA = (
    "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 "
    "(KHTML, like Gecko) Chrome/124.0 Safari/537.36"
)
_ISSUE_RE = re.compile(r"<td[^>]*>\s*(20\d{5})\s*</td>")
_BALL_RE = re.compile(r'<td class="chartBall\d+">\s*([^<]+?)\s*</td>')
_ROW_RE = re.compile(r"<tr[^>]*>(.*?)</tr>", re.S)


def parse_kl8_html(html: str) -> List[Tuple[str, List[int]]]:
    """解析走势页 HTML → [(期号, 20个开奖号)]，按期号升序、去重。"""
    records: Dict[str, List[int]] = {}
    for row in _ROW_RE.findall(html):
        m = _ISSUE_RE.search(row)
        if not m:
            continue
        issue = m.group(1)
        nums = sorted(int(x) for x in _BALL_RE.findall(row) if x.strip().isdigit())
        if len(nums) == K_DRAW and len(set(nums)) == K_DRAW and all(1 <= v <= N_POOL for v in nums):
            records[issue] = nums
    return [(k, records[k]) for k in sorted(records, key=int)]


def fetch_kl8_history(n_periods: int, timeout: float = 45.0) -> List[Tuple[str, List[int]]]:
    """
    爬取快乐8最近 n_periods 期历史开奖（含期号）。
    期数≤100 走精确预设(30/50/100)，否则取全量后截取最近 n 期。
    """
    n_periods = max(1, int(n_periods))
    if n_periods <= 30:
        expect = 30
    elif n_periods <= 50:
        expect = 50
    elif n_periods <= 100:
        expect = 100
    else:
        expect = 1000  # 非预设值 → 服务端返回全部历史
    url = f"{KL8_HISTORY_URL}?expect={expect}"
    req = urllib.request.Request(
        url,
        headers={"User-Agent": KL8_UA, "Referer": "https://datachart.500.com/kl8/"},
    )
    try:
        with urllib.request.urlopen(req, timeout=timeout) as resp:
            raw = resp.read()
    except urllib.error.HTTPError as e:
        raise TrueRandomError(f"爬取失败 HTTP {e.code}") from e
    except Exception as e:
        raise TrueRandomError(f"不会吧，不会吧！不会现在还有人断网吧！真可怜！要联网才能用") from e
    html = raw.decode("gb2312", errors="replace")
    records = parse_kl8_html(html)
    if not records:
        raise TrueRandomError("未解析到开奖数据，网页结构可能已变化。")
    return records[-n_periods:]


def _minmax_norm(d: Dict[int, float]) -> Dict[int, float]:
    vals = list(d.values())
    lo, hi = min(vals), max(vals)
    span = (hi - lo) or 1.0
    return {k: (v - lo) / span for k, v in d.items()}


# 可勾选的推理算法（综合分 = 已启用算法归一化得分的平均）
ALGO_LABELS: Dict[str, str] = {
    "freq": "全局频率(热号)",
    "recent": "近期热度(窗口)",
    "miss": "遗漏回补(冷号)",
    "bayes": "贝叶斯后验",
    "cooccur": "共现关联(与上期)",
    "markov": "马尔可夫链转移",
}
ALGO_KEYS = list(ALGO_LABELS.keys())


def _cooccurrence_with_last(draws: Sequence[Sequence[int]]) -> Dict[int, int]:
    """统计历史上与「最近一期开奖号」结伴出现的次数（共现关联）。"""
    if not draws:
        return {i: 0 for i in range(1, N_POOL + 1)}
    last = set(draws[-1])
    cooc: Counter = Counter()
    for d in draws:
        ds = set(d)
        overlap = ds & last
        if not overlap:
            continue
        for x in ds - last:
            cooc[x] += len(overlap)
    return {i: cooc.get(i, 0) for i in range(1, N_POOL + 1)}


def markov_transition_scores(draws: Sequence[Sequence[int]]) -> Dict[int, float]:
    """
    一阶马尔可夫链：把每期开奖视为状态集合，统计
    「期 t 出现 a → 期 t+1 出现 b」的转移频率 P(b|a)，
    再基于最近一期所含号码求和，得到各候选号的转移得分。
    """
    row_tot: Counter = Counter()
    trans: Dict[int, Counter] = defaultdict(Counter)
    for t in range(len(draws) - 1):
        cur, nxt = set(draws[t]), set(draws[t + 1])
        for a in cur:
            row_tot[a] += 1
            for b in nxt:
                trans[a][b] += 1
    scores: Dict[int, float] = {}
    last = set(draws[-1]) if draws else set()
    for x in range(1, N_POOL + 1):
        s = 0.0
        for a in last:
            if row_tot[a]:
                s += trans[a].get(x, 0) / row_tot[a]
        scores[x] = s
    return scores


def predict_next_draw(
    draws: Sequence[Sequence[int]],
    n_pick: int = 10,
    window: int = 30,
    enabled: Optional[Sequence[str]] = None,
) -> Dict[str, object]:
    """
    基于历史的统计推理（复盘工具，非真实预测）。
    enabled：用户勾选的算法集合；综合分 = 各启用算法归一化得分的平均。
    """
    T = len(draws)
    n_pick = max(1, min(N_PICK_MAX, int(n_pick)))
    keys = [k for k in ALGO_KEYS if (enabled is None and k in ("freq", "recent", "miss")) or (enabled is not None and k in set(enabled))]

    freq = frequency_map(draws)
    miss = missing_map(draws)
    recent = list(draws)[-window:] if window and window > 0 else list(draws)
    rc: Counter = Counter()
    for d in recent:
        rc.update(d)
    recent_freq = {i: rc.get(i, 0) for i in range(1, N_POOL + 1)}
    post = bayesian_posteriors(draws)
    cooc = _cooccurrence_with_last(draws)
    markov = markov_transition_scores(draws)

    raw: Dict[str, Dict[int, float]] = {
        "freq": {i: float(freq[i]) for i in range(1, N_POOL + 1)},
        "recent": {i: float(recent_freq[i]) for i in range(1, N_POOL + 1)},
        "miss": {i: float(miss[i]) for i in range(1, N_POOL + 1)},
        "bayes": {i: float(post[i]) for i in range(1, N_POOL + 1)},
        "cooccur": {i: float(cooc[i]) for i in range(1, N_POOL + 1)},
        "markov": markov,
    }
    subscores = {k: _minmax_norm(raw[k]) for k in keys}

    if subscores:
        score = {i: sum(s[i] for s in subscores.values()) / len(subscores) for i in range(1, N_POOL + 1)}
    else:
        score = {i: 0.0 for i in range(1, N_POOL + 1)}

    ranked = sorted(score.items(), key=lambda x: (x[1], x[0]), reverse=True)
    recommended = sorted(i for i, _ in ranked[:n_pick])
    empirical = {i: (freq[i] / T if T else P_SINGLE) for i in range(1, N_POOL + 1)}
    hot = sorted(range(1, N_POOL + 1), key=lambda i: freq[i], reverse=True)[:15]
    due = sorted(range(1, N_POOL + 1), key=lambda i: miss[i], reverse=True)[:15]
    algo_top = {
        k: sorted(range(1, N_POOL + 1), key=lambda i: (v[i], -i), reverse=True)[:n_pick]
        for k, v in subscores.items()
    }
    return {
        "T": T,
        "n_pick": n_pick,
        "enabled": keys,
        "score": score,
        "ranked": ranked,
        "recommended": recommended,
        "empirical": empirical,
        "freq": freq,
        "miss": miss,
        "hot": hot,
        "due": due,
        "subscores": subscores,
        "algo_top": algo_top,
    }


def backtest_predictor(
    draws: Sequence[Sequence[int]],
    n_pick: int = 10,
    window: int = 30,
    trials: int = 50,
    enabled: Optional[Sequence[str]] = None,
) -> Dict[str, float]:
    """用历史回测所选算法组合的真实命中水平，与理论期望对比（诚实展示无增益）。"""
    T = len(draws)
    n_pick = max(1, min(N_PICK_MAX, int(n_pick)))
    warm = window + 10
    if T < warm + 5:
        return {"trials": 0, "avg_hits": 0.0, "expected": n_pick * P_SINGLE}
    start = max(warm, T - trials)
    hits: List[int] = []
    for idx in range(start, T):
        pred = predict_next_draw(list(draws)[:idx], n_pick, window, enabled)["recommended"]
        hits.append(len(set(pred) & set(draws[idx])))
    avg = sum(hits) / len(hits) if hits else 0.0
    return {
        "trials": len(hits),
        "avg_hits": avg,
        "expected": n_pick * P_SINGLE,
        "max_hits": max(hits) if hits else 0,
        "min_hits": min(hits) if hits else 0,
    }


# ══════════════════════════════════════════════════════════════
# UI
# ══════════════════════════════════════════════════════════════

class Happy8App(tk.Tk):
    def __init__(self):
        super().__init__()
        self.title("摇奖模拟器 · 快乐8")
        self.geometry("1100x860")
        self.minsize(960, 760)
        self.configure(bg=BG)
        try:
            self.iconbitmap(resource_path("kuaile8.ico"))
        except tk.TclError:
            pass

        self.selected: set = set()
        self.killed: set = set()  # 快乐8 杀号：开奖永不出现
        self.click_mode = tk.StringVar(value="pick")  # pick | kill
        self.drawn: List[int] = []
        self.history: List[List[int]] = []
        self.is_drawing = False
        self.ball_btns: Dict[int, tk.Button] = {}
        self.shake_job = None

        # 拖动选号/杀号状态
        self._drag_active = False
        self._drag_target = "pick"      # pick | kill
        self._drag_action = "add"       # add | remove
        self._drag_visited: set = set()
        self._ball_widget_num: Dict[int, int] = {}  # widget id -> 号码

        # 真实历史数据（爬取）
        self.crawled: List[Tuple[str, List[int]]] = []
        # 推理算法勾选状态（默认启用 频率/近期/遗漏）
        self.algo_vars: Dict[str, tk.BooleanVar] = {}
        self._last_prediction: Optional[Dict[str, object]] = None

        self._setup_style()
        self._build()
        self._center()
        self.protocol("WM_DELETE_WINDOW", self.destroy)

    def _center(self):
        self.update_idletasks()
        w, h = self.winfo_width(), self.winfo_height()
        x = (self.winfo_screenwidth() - w) // 2
        y = max(0, (self.winfo_screenheight() - h) // 2 - 16)
        self.geometry(f"+{x}+{y}")

    def _setup_style(self):
        style = ttk.Style(self)
        try:
            style.theme_use("clam")
        except tk.TclError:
            pass
        style.configure("TNotebook", background=BG, borderwidth=0)
        style.configure("TNotebook.Tab", background=CARD, foreground=TEXT, padding=(14, 6), font=("Microsoft YaHei UI", 10))
        style.map("TNotebook.Tab", background=[("selected", GOLD_DIM)], foreground=[("selected", "#1a1a2e")])
        style.configure("TFrame", background=BG)
        style.configure("Card.TFrame", background=CARD)
        style.configure("TLabel", background=BG, foreground=TEXT, font=("Microsoft YaHei UI", 10))
        style.configure("Muted.TLabel", background=BG, foreground=MUTED, font=("Microsoft YaHei UI", 9))
        style.configure("Card.TLabel", background=CARD, foreground=TEXT, font=("Microsoft YaHei UI", 10))
        style.configure("Gold.TLabel", background=CARD, foreground=GOLD, font=("Microsoft YaHei UI", 11, "bold"))
        style.configure("Title.TLabel", background=BG, foreground=GOLD, font=("Microsoft YaHei UI", 20, "bold"))
        style.configure("TProgressbar", troughcolor=INPUT, background=GOLD)

    def _build(self):
        head = ttk.Frame(self, padding=(20, 16, 20, 8))
        head.pack(fill="x")
        ttk.Label(head, text="摇奖模拟器 · 快乐8", style="Title.TLabel").pack(anchor="w")
        ttk.Label(
            head,
            text="注意哈！！不保证百分百中，自己斟酌使用。",
            style="Muted.TLabel",
        ).pack(anchor="w", pady=(4, 0))

        self.nb = ttk.Notebook(self)
        self.nb.pack(fill="both", expand=True, padx=16, pady=(8, 16))

        self.tab_play = ttk.Frame(self.nb)
        self.tab_crawl = ttk.Frame(self.nb)
        self.nb.add(self.tab_play, text="模拟摇号")
        self.nb.add(self.tab_crawl, text="联网获取历史开奖数据")

        self._build_play_tab()
        self._build_crawl_tab()

    # ── Tab 1: 开奖 ───────────────────────────────────────────
    def _build_play_tab(self):
        root = ttk.Frame(self.tab_play, padding=12)
        root.pack(fill="both", expand=True)

        left = tk.Frame(root, bg=CARD, highlightbackground=BORDER, highlightthickness=1)
        left.pack(side="left", fill="both", expand=True, padx=(0, 8))

        top = tk.Frame(left, bg=CARD)
        top.pack(fill="x", padx=12, pady=10)
        tk.Label(top, text="号码盘（投注/杀号）", bg=CARD, fg=GOLD, font=("Microsoft YaHei UI", 11, "bold")).pack(side="left")
        self.pick_info = tk.Label(top, text="已选 0 / 10", bg=CARD, fg=MUTED, font=("Microsoft YaHei UI", 10))
        self.pick_info.pack(side="right")

        mode_row = tk.Frame(left, bg=CARD)
        mode_row.pack(fill="x", padx=12, pady=(0, 6))
        tk.Label(mode_row, text="点击模式（可按住拖动连选）：", bg=CARD, fg=MUTED, font=("Microsoft YaHei UI", 9)).pack(side="left")
        tk.Radiobutton(
            mode_row, text="投注选号", variable=self.click_mode, value="pick",
            command=self._refresh_pick_ui, bg=CARD, fg=TEXT, selectcolor=INPUT,
            activebackground=CARD, activeforeground=GOLD, font=("Microsoft YaHei UI", 9),
        ).pack(side="left", padx=4)
        tk.Radiobutton(
            mode_row, text="杀号（移出奖池）", variable=self.click_mode, value="kill",
            command=self._refresh_pick_ui, bg=CARD, fg=KILL_FG, selectcolor=INPUT,
            activebackground=CARD, activeforeground=KILL_FG, font=("Microsoft YaHei UI", 9),
        ).pack(side="left", padx=4)
        self.kill_info = tk.Label(mode_row, text="杀号 0｜奖池 80", bg=CARD, fg=KILL_FG, font=("Microsoft YaHei UI", 9))
        self.kill_info.pack(side="right")

        grid = tk.Frame(left, bg=CARD)
        grid.pack(padx=10, pady=(0, 8))
        for i in range(1, N_POOL + 1):
            r, c = divmod(i - 1, 10)
            btn = tk.Button(
                grid, text=f"{i:02d}", width=4,
                font=("Consolas", 9, "bold"),
                bd=0, pady=4, cursor="hand2",
            )
            btn.grid(row=r, column=c, padx=2, pady=2)
            self.ball_btns[i] = btn
            self._ball_widget_num[id(btn)] = i
            btn.bind("<ButtonPress-1>", lambda e, n=i: self._on_ball_press(n, e))
            btn.bind("<B1-Motion>", self._on_ball_drag)
            btn.bind("<ButtonRelease-1>", self._on_ball_release)
            self._style_ball_btn(i, False)

        tools = tk.Frame(left, bg=CARD)
        tools.pack(fill="x", padx=12, pady=(0, 12))
        for n in range(1, 11):
            tk.Button(
                tools, text=f"机选{n}", width=5, command=lambda x=n: self._random_pick(x),
                bg=INPUT, fg=TEXT, bd=0, padx=2, pady=6, cursor="hand2",
                font=("Microsoft YaHei UI", 9),
            ).pack(side="left", padx=2)
        tk.Button(
            tools, text="遗传均衡选号", command=self._genetic_pick,
            bg=INPUT, fg=GOLD, bd=0, padx=10, pady=6, cursor="hand2",
            font=("Microsoft YaHei UI", 9),
        ).pack(side="left", padx=3)
        tk.Button(
            tools, text="清空投注", command=self._clear_picks,
            bg=INPUT, fg=RED, bd=0, padx=10, pady=6, cursor="hand2",
            font=("Microsoft YaHei UI", 9),
        ).pack(side="left", padx=3)
        tk.Button(
            tools, text="清空杀号", command=self._clear_kills,
            bg=INPUT, fg=KILL_FG, bd=0, padx=10, pady=6, cursor="hand2",
            font=("Microsoft YaHei UI", 9),
        ).pack(side="left", padx=3)

        right = tk.Frame(root, bg=CARD, highlightbackground=BORDER, highlightthickness=1, width=420)
        right.pack(side="right", fill="both")
        right.pack_propagate(False)

        tk.Label(right, text="开奖仓 · 每期抽取 20 码", bg=CARD, fg=GOLD,
                 font=("Microsoft YaHei UI", 11, "bold")).pack(anchor="w", padx=14, pady=(12, 6))

        self.drum = tk.Canvas(right, height=150, bg=INPUT, highlightthickness=1, highlightbackground=GOLD_DIM)
        self.drum.pack(fill="x", padx=14)
        self._paint_drum_idle()

        self.draw_btn = tk.Button(
            right, text="开始开奖（抽 20 个）", command=self.start_draw,
            bg=RED, fg="white", activebackground="#c0392b",
            font=("Microsoft YaHei UI", 13, "bold"), bd=0, pady=12, cursor="hand2",
        )
        self.draw_btn.pack(fill="x", padx=14, pady=12)

        self.status = tk.Label(right, text="请先选择 1~10 个投注号码", bg=CARD, fg=MUTED,
                               font=("Microsoft YaHei UI", 10))
        self.status.pack(anchor="w", padx=14)

        self.hit_label = tk.Label(right, text="命中：—", bg=CARD, fg=GOLD,
                                  font=("Microsoft YaHei UI", 16, "bold"))
        self.hit_label.pack(anchor="w", padx=14, pady=(10, 4))

        self.feature_label = tk.Label(right, text="", bg=CARD, fg=MUTED, justify="left",
                                      font=("Microsoft YaHei UI", 9))
        self.feature_label.pack(anchor="w", padx=14, pady=(0, 6))

        tk.Label(right, text="开奖号码", bg=CARD, fg=MUTED, font=("Microsoft YaHei UI", 9)).pack(anchor="w", padx=14)
        self.drawn_box = tk.Frame(right, bg=CARD)
        self.drawn_box.pack(fill="x", padx=12, pady=4)

        tk.Label(right, text="命中明细", bg=CARD, fg=MUTED, font=("Microsoft YaHei UI", 9)).pack(anchor="w", padx=14, pady=(8, 0))
        self.hit_box = tk.Frame(right, bg=CARD)
        self.hit_box.pack(fill="x", padx=12, pady=4)

        self.prob_summary = tk.Label(right, text="", bg=CARD, fg=BLUE, justify="left",
                                     font=("Microsoft YaHei UI", 9))
        self.prob_summary.pack(anchor="w", padx=14, pady=(8, 14))

    def _style_ball_btn(self, n: int, selected: bool, hit: Optional[bool] = None):
        btn = self.ball_btns[n]
        if n in self.killed:
            btn.configure(bg=KILL, fg=KILL_FG, activebackground=KILL, text=f"{n:02d}×")
            return
        btn.configure(text=f"{n:02d}")
        if hit is True:
            btn.configure(bg=HIT, fg="white", activebackground=HIT)
        elif hit is False and selected:
            btn.configure(bg=MISS, fg=TEXT, activebackground=MISS)
        elif selected:
            btn.configure(bg=GOLD, fg="#1a1a2e", activebackground=GOLD_DIM)
        else:
            btn.configure(bg=INPUT, fg=TEXT, activebackground=BORDER)

    def _toggle_pick(self, n: int):
        if self.is_drawing:
            return
        if self.click_mode.get() == "kill":
            if n in self.killed:
                self.killed.remove(n)
            else:
                # 至少保留 2 个可开奖号码
                if N_POOL - (len(self.killed) + 1) < KILL_POOL_MIN:
                    messagebox.showinfo("杀号过多", f"奖池至少保留 {KILL_POOL_MIN} 个号码。")
                    return
                self.killed.add(n)
                self.selected.discard(n)
            self._refresh_pick_ui()
            return
        if n in self.killed:
            messagebox.showinfo("已杀号", f"{n:02d} 已被杀号，不能投注。可切换到「杀号」模式取消。")
            return
        if n in self.selected:
            self.selected.remove(n)
        else:
            if len(self.selected) >= N_PICK_MAX:
                messagebox.showinfo("选号上限", "快乐8 单注最多自选 10 个号码。")
                return
            self.selected.add(n)
        self._refresh_pick_ui()

    def _on_ball_press(self, n: int, event):
        """按下：确定拖动作用域（选号/杀号）与动作（加/减），并作用于当前号。"""
        if self.is_drawing:
            return
        self._drag_active = True
        self._drag_visited = set()
        if self.click_mode.get() == "kill":
            self._drag_target = "kill"
            self._drag_action = "remove" if n in self.killed else "add"
        else:
            self._drag_target = "pick"
            self._drag_action = "remove" if n in self.selected else "add"
        self._drag_apply(n)
        self._refresh_pick_ui()

    def _on_ball_drag(self, event):
        """拖动：Tk 隐式抓取会把 Motion 派发给按下的按钮，用 containing 解析当前号。"""
        if not self._drag_active or self.is_drawing:
            return
        try:
            w = self.winfo_containing(event.x_root, event.y_root)
        except (KeyError, tk.TclError):
            return
        n = self._ball_widget_num.get(id(w)) if w is not None else None
        if n is None:
            return
        self._drag_apply(n)

    def _on_ball_release(self, event):
        if not self._drag_active:
            return
        self._drag_active = False
        self._drag_visited = set()
        self._refresh_pick_ui()

    def _drag_apply(self, n: int):
        """按拖动动作对号码 n 加/减，静默遵守上下限（不弹窗，避免拖动被打断）。"""
        if n in self._drag_visited:
            return
        if self._drag_target == "kill":
            if self._drag_action == "add":
                if n in self.killed:
                    return
                if N_POOL - (len(self.killed) + 1) < KILL_POOL_MIN:
                    return  # 奖池须至少保留 2 个
                self.killed.add(n)
                self.selected.discard(n)
            else:
                if n not in self.killed:
                    return
                self.killed.discard(n)
        else:  # pick
            if n in self.killed:
                return  # 已杀号不可投注
            if self._drag_action == "add":
                if n in self.selected:
                    return
                if len(self.selected) >= N_PICK_MAX:
                    return
                self.selected.add(n)
            else:
                if n not in self.selected:
                    return
                self.selected.discard(n)
        self._drag_visited.add(n)
        self._refresh_pick_ui()

    def _random_pick(self, n: int):
        if self.is_drawing:
            return
        pool = [i for i in range(1, N_POOL + 1) if i not in self.killed]
        if len(pool) < n:
            messagebox.showinfo("号码不足", f"去掉杀号后只剩 {len(pool)} 个，无法机选 {n} 个。")
            return
        self.selected = set(random.sample(pool, n))
        self._refresh_pick_ui()

    def _genetic_pick(self):
        if self.is_drawing:
            return
        n = len(self.selected) or 7
        n = max(N_PICK_MIN, min(N_PICK_MAX, n))
        pool = [i for i in range(1, N_POOL + 1) if i not in self.killed]
        if len(pool) < n:
            messagebox.showinfo("号码不足", f"去掉杀号后只剩 {len(pool)} 个，无法生成 {n} 码。")
            return
        ticket = genetic_balanced_ticket(n)
        # 剔除杀号并补足
        cleaned = [x for x in ticket if x not in self.killed]
        for x in pool:
            if len(cleaned) >= n:
                break
            if x not in cleaned:
                cleaned.append(x)
        self.selected = set(sorted(cleaned)[:n])
        self._refresh_pick_ui()
        self.status.configure(text=f"遗传算法已生成 {n} 码均衡组合（已避开杀号）", fg=GOLD)

    def _clear_picks(self):
        if self.is_drawing:
            return
        self.selected.clear()
        self.drawn.clear()
        self._refresh_pick_ui()
        self._clear_result_widgets()
        self.hit_label.configure(text="命中：—")
        self.status.configure(text="请先选择 1~10 个投注号码", fg=MUTED)
        self.feature_label.configure(text="")
        self.prob_summary.configure(text="")
        self._paint_drum_idle()

    def _clear_kills(self):
        if self.is_drawing:
            return
        self.killed.clear()
        self._refresh_pick_ui()
        self.status.configure(text="已清空杀号，奖池恢复 80 个。", fg=MUTED)

    def _refresh_pick_ui(self):
        for i in range(1, N_POOL + 1):
            self._style_ball_btn(i, i in self.selected)
        self.pick_info.configure(text=f"已选 {len(self.selected)} / {N_PICK_MAX}")
        remain = N_POOL - len(self.killed)
        self.kill_info.configure(text=f"杀号 {len(self.killed)}｜奖池 {remain}")

    def _clear_result_widgets(self):
        for box in (self.drawn_box, self.hit_box):
            for w in box.winfo_children():
                w.destroy()

    def _paint_drum_idle(self):
        self.drum.delete("all")
        w = max(self.drum.winfo_width(), 360)
        h = 150
        self.drum.create_oval(w * 0.15, 20, w * 0.85, h - 10, fill="#1e2a4a", outline=GOLD_DIM)
        sample = random.sample(range(1, N_POOL + 1), 16)
        for i, num in enumerate(sample):
            x = 40 + (i % 8) * ((w - 80) / 7)
            y = 45 + (i // 8) * 50
            self._oval_ball(self.drum, x, y, 14, num)

    def _oval_ball(self, canvas, x, y, r, num, fill=None):
        c1, c2 = BALL_PALETTE[num % len(BALL_PALETTE)]
        if fill:
            c1 = fill
        canvas.create_oval(x - r, y - r, x + r, y + r, fill=c1, outline=c2)
        canvas.create_text(x, y, text=f"{num:02d}", fill="white", font=("Consolas", 8, "bold"))

    def _chip(self, parent, num: int, hit: bool = False):
        bg = HIT if hit else INPUT
        fg = "white" if hit else TEXT
        lab = tk.Label(parent, text=f"{num:02d}", bg=bg, fg=fg, width=3,
                       font=("Consolas", 10, "bold"), padx=2, pady=4)
        lab.pack(side="left", padx=2, pady=2)

    def start_draw(self):
        if self.is_drawing:
            return
        if not self.selected:
            messagebox.showinfo("未选号", "请先选择 1~10 个投注号码。")
            return
        if self.selected & self.killed:
            messagebox.showinfo("含杀号", "投注号中包含已杀号码，请先取消杀号或改选。")
            return
        if N_POOL - len(self.killed) < KILL_POOL_MIN:
            messagebox.showerror("杀号过多", f"奖池至少保留 {KILL_POOL_MIN} 个号码。")
            return
        self.is_drawing = True
        self.draw_btn.configure(state="disabled", text="开奖中...", bg=GOLD_DIM, fg="#1a1a2e")
        tip = f"（已杀 {len(self.killed)} 码）" if self.killed else ""
        self.status.configure(text=f"无放回抽样进行中…{tip}", fg=GOLD)
        self._clear_result_widgets()
        self._shake(0, max_steps=18)

    def _shake(self, step: int, max_steps: int):
        self.drum.delete("all")
        w = max(self.drum.winfo_width(), 360)
        self.drum.create_oval(w * 0.15, 20, w * 0.85, 140, fill="#1e2a4a", outline=GOLD)
        pool = [i for i in range(1, N_POOL + 1) if i not in self.killed]
        sample_n = min(16, len(pool))
        sample = random.sample(pool, sample_n) if sample_n else []
        dx = random.choice([-3, -1, 1, 3])
        for i, num in enumerate(sample):
            x = 40 + (i % 8) * ((w - 80) / 7) + dx
            y = 45 + (i // 8) * 50 + random.choice([-2, 0, 2])
            self._oval_ball(self.drum, x, y, 14, num)
        if step < max_steps:
            self.after(55, lambda: self._shake(step + 1, max_steps))
        else:
            self._finish_draw()

    def _finish_draw(self):
        try:
            self.drawn = draw_official(self.killed)
        except ValueError as e:
            self.is_drawing = False
            self.draw_btn.configure(state="normal", text="开始开奖（抽 20 个）", bg=RED, fg="white")
            messagebox.showerror("开奖失败", str(e))
            return
        self.history.append(self.drawn[:])
        # 保留最近 500 期供统计
        if len(self.history) > 500:
            self.history = self.history[-500:]

        hits = sorted(set(self.selected) & set(self.drawn))
        k = len(hits)
        n = len(self.selected)
        k_drawn = len(self.drawn)
        p_k = hypergeometric_pmf(N_POOL, k_drawn, n, k)
        e_x = hypergeometric_mean(N_POOL, k_drawn, n)

        # 鼓面展示开奖号
        self.drum.delete("all")
        w = max(self.drum.winfo_width(), 360)
        for i, num in enumerate(self.drawn):
            x = 28 + (i % 10) * ((w - 40) / 9)
            y = 40 + (i // 10) * 55
            fill = HIT if num in self.selected else None
            self._oval_ball(self.drum, x, y, 16, num, fill=fill)

        for num in self.drawn:
            self._chip(self.drawn_box, num, hit=(num in self.selected))

        if hits:
            for num in hits:
                self._chip(self.hit_box, num, hit=True)
        else:
            tk.Label(self.hit_box, text="本期未命中", bg=CARD, fg=MUTED,
                     font=("Microsoft YaHei UI", 9)).pack(anchor="w")

        # 选号区高亮命中/未中
        for i in range(1, N_POOL + 1):
            if i in self.selected:
                self._style_ball_btn(i, True, hit=(i in hits))
            else:
                self._style_ball_btn(i, False)

        odd, even = parity_stats(self.drawn)
        small, big = size_stats(self.drawn)
        z1, z2, z3, z4 = zone_stats(self.drawn)
        self.hit_label.configure(text=f"命中：{k} / {n}")
        self.feature_label.configure(
            text=(
                f"开奖特征｜奇数 {odd} : 偶数 {even}（期望各≈10）\n"
                f"大小号｜小(1-40) {small} : 大(41-80) {big}\n"
                f"四区｜{z1}-{z2}-{z3}-{z4}｜和值 {sum(self.drawn)}"
            )
        )
        self.prob_summary.configure(
            text=(
                f"超几何 P(X={k}) = {fmt_pct(p_k)}\n"
                f"期望命中 E[X]= nK/N = {e_x:.4f}\n"
                f"公式：C({k_drawn},{k})·C({N_POOL - k_drawn},{n - k}) / C({N_POOL},{n})"
            )
        )
        kill_tip = f" · 已杀 {len(self.killed)} 码" if self.killed else ""
        self.status.configure(
            text=f"第 {len(self.history)} 期模拟完成 · 无放回抽取 {k_drawn} 码{kill_tip}",
            fg=GREEN,
        )
        self.is_drawing = False
        self.draw_btn.configure(state="normal", text="开始开奖（抽 20 个）", bg=RED, fg="white")

    # ── Tab 6: 历史数据爬取 · 分析推理 ────────────────────────
    def _build_crawl_tab(self):
        wrap = ttk.Frame(self.tab_crawl, padding=14)
        wrap.pack(fill="both", expand=True)

        ttk.Label(wrap, text="这里有根据历史数据推理的算法，哈哈哈哈！！！我厉害吧！！这个获取功能联网使用的，没网别瞎霍霍", style="Title.TLabel").pack(anchor="w")

        ctrl = tk.Frame(wrap, bg=CARD, highlightbackground=BORDER, highlightthickness=1)
        ctrl.pack(fill="x", pady=(0, 10))
        row = tk.Frame(ctrl, bg=CARD)
        row.pack(fill="x", padx=12, pady=10)
        tk.Label(row, text="爬取期数", bg=CARD, fg=TEXT, font=("Microsoft YaHei UI", 10)).pack(side="left")
        self.crawl_n = tk.IntVar(value=100)
        tk.Spinbox(row, from_=1, to=1700, textvariable=self.crawl_n, width=7,
                   font=("Consolas", 11)).pack(side="left", padx=8)
        tk.Label(row, text="（1~1700，>100 会下载全量再截取，稍慢）", bg=CARD, fg=MUTED,
                 font=("Microsoft YaHei UI", 8)).pack(side="left")
        self.crawl_btn = tk.Button(
            row, text="开始爬取", command=self._crawl_start,
            bg=BLUE, fg="white", bd=0, padx=16, pady=6, cursor="hand2",
            font=("Microsoft YaHei UI", 10, "bold"),
        )
        self.crawl_btn.pack(side="left", padx=12)
        tk.Button(
            row, text="导入本程序", command=self._crawl_import,
            bg=INPUT, fg=GOLD, bd=0, padx=14, pady=6, cursor="hand2",
            font=("Microsoft YaHei UI", 10),
        ).pack(side="left", padx=4)

        self.crawl_status = tk.Label(wrap, text="尚未爬取。", bg=BG, fg=MUTED,
                                     font=("Microsoft YaHei UI", 10), anchor="w")
        self.crawl_status.pack(fill="x", pady=(0, 2))
        self.import_info = tk.Label(wrap, text="已导入真实历史：0 期", bg=BG, fg=MUTED,
                                    font=("Microsoft YaHei UI", 9), anchor="w")
        self.import_info.pack(fill="x", pady=(0, 8))

        body = tk.Frame(wrap, bg=BG)
        body.pack(fill="both", expand=True)

        left = tk.Frame(body, bg=CARD, highlightbackground=BORDER, highlightthickness=1)
        left.pack(side="left", fill="both", expand=True, padx=(0, 6))
        lh = tk.Frame(left, bg=CARD)
        lh.pack(fill="x", padx=12, pady=(10, 4))
        tk.Label(lh, text="爬取数据（期号 + 20 码）", bg=CARD, fg=GOLD,
                 font=("Microsoft YaHei UI", 11, "bold")).pack(side="left")
        tk.Button(lh, text="复制", command=self._crawl_copy,
                  bg=INPUT, fg=TEXT, bd=0, padx=8, pady=2, cursor="hand2",
                  font=("Microsoft YaHei UI", 8)).pack(side="right")
        lscroll_wrap = tk.Frame(left, bg=CARD)
        lscroll_wrap.pack(fill="both", expand=True, padx=10, pady=(0, 10))
        ls = ttk.Scrollbar(lscroll_wrap)
        ls.pack(side="right", fill="y")
        self.crawl_text = tk.Text(lscroll_wrap, bg=INPUT, fg=TEXT, bd=0,
                                  font=("Consolas", 10), yscrollcommand=ls.set, wrap="none")
        self.crawl_text.pack(side="left", fill="both", expand=True)
        ls.configure(command=self.crawl_text.yview)
        self.crawl_text.insert("end", "点击「开始爬取」获取真实历史开奖…\n")
        self.crawl_text.configure(state="disabled")

        right = tk.Frame(body, bg=CARD, highlightbackground=BORDER, highlightthickness=1)
        right.pack(side="left", fill="both", expand=True, padx=(6, 0))
        rh = tk.Frame(right, bg=CARD)
        rh.pack(fill="x", padx=12, pady=(10, 4))
        tk.Label(rh, text="分析推理 · 下一期", bg=CARD, fg=GOLD,
                 font=("Microsoft YaHei UI", 11, "bold")).pack(side="left")
        rbar = tk.Frame(right, bg=CARD)
        rbar.pack(fill="x", padx=12, pady=(0, 6))
        tk.Label(rbar, text="推荐选号数", bg=CARD, fg=MUTED, font=("Microsoft YaHei UI", 9)).pack(side="left")
        self.predict_n = tk.IntVar(value=10)
        tk.Spinbox(rbar, from_=1, to=10, textvariable=self.predict_n, width=5,
                   font=("Consolas", 10)).pack(side="left", padx=6)
        tk.Label(rbar, text="回看窗口", bg=CARD, fg=MUTED, font=("Microsoft YaHei UI", 9)).pack(side="left", padx=(8, 0))
        self.predict_win = tk.IntVar(value=30)
        tk.Spinbox(rbar, from_=5, to=200, textvariable=self.predict_win, width=5,
                   font=("Consolas", 10)).pack(side="left", padx=6)
        self.predict_btn = tk.Button(
            rbar, text="分析推理", command=self._crawl_predict,
            bg=GOLD_DIM, fg="#1a1a2e", bd=0, padx=12, pady=4, cursor="hand2",
            font=("Microsoft YaHei UI", 9, "bold"),
        )
        self.predict_btn.pack(side="left", padx=8)
        tk.Button(
            rbar, text="推荐→选号区", command=self._crawl_apply_picks,
            bg=INPUT, fg=GREEN, bd=0, padx=10, pady=4, cursor="hand2",
            font=("Microsoft YaHei UI", 9),
        ).pack(side="left")
        tk.Button(
            rbar, text="推荐→开奖栏·自动杀号", command=self._crawl_apply_with_kill,
            bg=INPUT, fg=KILL_FG, bd=0, padx=10, pady=4, cursor="hand2",
            font=("Microsoft YaHei UI", 9),
        ).pack(side="left", padx=(6, 0))

        algo_box = tk.Frame(right, bg=CARD, highlightbackground=BORDER, highlightthickness=1)
        algo_box.pack(fill="x", padx=10, pady=(0, 6))
        ab_head = tk.Frame(algo_box, bg=CARD)
        ab_head.pack(fill="x", padx=8, pady=(6, 2))
        tk.Label(ab_head, text="推理算法（勾选参与综合评分，综合分=各启用算法归一化得分的均值）",
                 bg=CARD, fg=GOLD, font=("Microsoft YaHei UI", 9, "bold")).pack(side="left")
        tk.Button(ab_head, text="全选", command=lambda: self._set_all_algos(True),
                  bg=INPUT, fg=TEXT, bd=0, padx=6, pady=1, cursor="hand2",
                  font=("Microsoft YaHei UI", 8)).pack(side="right", padx=(4, 8))
        tk.Button(ab_head, text="全不选", command=lambda: self._set_all_algos(False),
                  bg=INPUT, fg=TEXT, bd=0, padx=6, pady=1, cursor="hand2",
                  font=("Microsoft YaHei UI", 8)).pack(side="right")
        ab_grid = tk.Frame(algo_box, bg=CARD)
        ab_grid.pack(fill="x", padx=8, pady=(0, 8))
        defaults = {"freq", "recent", "miss"}
        for idx, key in enumerate(ALGO_KEYS):
            var = tk.BooleanVar(value=(key in defaults))
            self.algo_vars[key] = var
            tk.Checkbutton(
                ab_grid, text=ALGO_LABELS[key], variable=var,
                bg=CARD, fg=TEXT, selectcolor=INPUT, activebackground=CARD,
                activeforeground=GOLD, font=("Microsoft YaHei UI", 9),
            ).grid(row=idx // 3, column=idx % 3, sticky="w", padx=6, pady=2)

        rscroll_wrap = tk.Frame(right, bg=CARD)
        rscroll_wrap.pack(fill="both", expand=True, padx=10, pady=(0, 10))
        rs = ttk.Scrollbar(rscroll_wrap)
        rs.pack(side="right", fill="y")
        self.predict_text = tk.Text(rscroll_wrap, bg=INPUT, fg=TEXT, bd=0,
                                    font=("Consolas", 10), yscrollcommand=rs.set, wrap="word")
        self.predict_text.pack(side="left", fill="both", expand=True)
        rs.configure(command=self.predict_text.yview)
        self.predict_text.insert("end", "先爬取数据，再点击「分析推理」。\n")
        self.predict_text.configure(state="disabled")

        self._last_prediction: Optional[Dict[str, object]] = None

    def _crawl_start(self):
        try:
            n = int(self.crawl_n.get())
        except (TypeError, ValueError, tk.TclError):
            messagebox.showerror("期数无效", "请输入有效的爬取期数。")
            return
        n = max(1, min(1700, n))
        self.crawl_btn.configure(state="disabled", text="爬取中…", bg=GOLD_DIM, fg="#1a1a2e")
        self.crawl_status.configure(text=f"正在从 500彩票网 爬取最近 {n} 期…", fg=GOLD)
        self.update_idletasks()
        try:
            records = fetch_kl8_history(n)
        except TrueRandomError as e:
            self.crawl_status.configure(text=f"爬取失败：{e}", fg=RED)
            messagebox.showerror("爬取失败", str(e))
            return
        except Exception as e:
            self.crawl_status.configure(text=f"爬取异常：{e}", fg=RED)
            messagebox.showerror("爬取异常", str(e))
            return
        finally:
            self.crawl_btn.configure(state="normal", text="开始爬取", bg=BLUE, fg="white")

        self.crawled = records
        first, last = records[0][0], records[-1][0]
        self.crawl_status.configure(
            text=f"爬取成功：{len(records)} 期（{first} ~ {last}）。可「导入本程序」或「分析推理」。", fg=GREEN,
        )
        self.crawl_text.configure(state="normal")
        self.crawl_text.delete("1.0", "end")
        for issue, nums in records:
            self.crawl_text.insert("end", f"{issue}  " + " ".join(f"{x:02d}" for x in nums) + "\n")
        self.crawl_text.configure(state="disabled")
        self.crawl_text.see("end")

    def _crawl_copy(self):
        if not self.crawled:
            messagebox.showinfo("无内容", "还没有爬取数据可复制。")
            return
        text = "\n".join(f"{i},{','.join(str(x) for x in n)}" for i, n in self.crawled)
        self.clipboard_clear()
        self.clipboard_append(text)
        self.crawl_status.configure(text=f"已复制 {len(self.crawled)} 期（CSV：期号,号码…）到剪贴板。", fg=GREEN)

    def _crawl_import(self):
        if not self.crawled:
            messagebox.showinfo("未爬取", "请先爬取历史数据再导入。")
            return
        self.history = [nums[:] for _, nums in self.crawled]
        self.import_info.configure(
            text=f"已导入真实历史：{len(self.history)} 期（{self.crawled[0][0]} ~ {self.crawled[-1][0]}）",
            fg=GREEN,
        )
        self.crawl_status.configure(
            text=f"已导入 {len(self.history)} 期真实数据到程序，可点「分析推理」。", fg=GREEN,
        )

    def _set_all_algos(self, value: bool):
        for var in self.algo_vars.values():
            var.set(value)

    def _enabled_algos(self) -> List[str]:
        return [k for k in ALGO_KEYS if self.algo_vars[k].get()]

    def _crawl_predict(self):
        if len(self.crawled) < 10:
            messagebox.showinfo("样本不足", "请先爬取至少 10 期数据。")
            return
        enabled = self._enabled_algos()
        if not enabled:
            messagebox.showinfo("未选算法", "请至少勾选一个推理算法。")
            return
        try:
            n_pick = max(1, min(N_PICK_MAX, int(self.predict_n.get())))
            window = max(5, min(200, int(self.predict_win.get())))
        except (TypeError, ValueError, tk.TclError):
            messagebox.showerror("参数无效", "推荐选号数须 1~10，回看窗口须 5~200。")
            return
        draws = [nums for _, nums in self.crawled]
        pred = predict_next_draw(draws, n_pick=n_pick, window=window, enabled=enabled)
        self._last_prediction = pred
        last_issue = self.crawled[-1][0]
        bt = backtest_predictor(draws, n_pick=n_pick, window=window, trials=50, enabled=enabled)
        algo_names = " + ".join(ALGO_LABELS[k] for k in pred["enabled"])  # type: ignore

        self.predict_text.configure(state="normal")
        self.predict_text.delete("1.0", "end")
        w = self.predict_text.insert
        w("end", f"样本：{pred['T']} 期（最新 {last_issue}）｜回看窗口 {window}\n")
        w("end", f"启用算法：{algo_names}\n")
        w("end", "═" * 46 + "\n")
        w("end", f"【推荐下一期 {n_pick} 码】（综合分 = 启用算法归一化得分均值）\n")
        w("end", "  " + " ".join(f"{x:02d}" for x in pred["recommended"]) + "\n\n")

        w("end", "【各算法单独 Top（勾选者）】\n")
        for k in pred["enabled"]:  # type: ignore
            tops = pred["algo_top"][k]  # type: ignore
            w("end", f"  · {ALGO_LABELS[k]}: " + " ".join(f"{x:02d}" for x in tops) + "\n")
        w("end", "\n【热号 Top15 · 历史高频】\n")
        w("end", "  " + " ".join(f"{x:02d}" for x in pred["hot"]) + "\n")
        w("end", "【遗漏 Top15 · 长期未出（回补候选）】\n")
        w("end", "  " + " ".join(f"{x:02d}" for x in pred["due"]) + "\n\n")

        w("end", "═" * 46 + "\n")
        w("end", "【概率】\n")
        w("end", f"  · 理论：单号每期出现概率 = 20/80 = {P_SINGLE:.2%}（各号相同，历史不改变它）\n")
        w("end", f"  · 经验出现率（样本内）最高 / 最低：\n")
        emp = pred["empirical"]
        hi = max(range(1, N_POOL + 1), key=lambda i: emp[i])
        lo = min(range(1, N_POOL + 1), key=lambda i: emp[i])
        w("end", f"      {hi:02d}: {emp[hi]:.2%}    {lo:02d}: {emp[lo]:.2%}\n")
        w("end", f"  · 若投注推荐 {n_pick} 码，命中数 X ~ 超几何(N=80,K=20,n={n_pick})：\n")
        ex = hypergeometric_mean(N_POOL, K_DRAW, n_pick)
        w("end", f"      期望命中 E[X] = {ex:.3f}\n")
        for k, p in hypergeometric_table(N_POOL, K_DRAW, n_pick):
            w("end", f"      P(X={k}) = {fmt_pct(p)}\n")

        w("end", "\n" + "═" * 46 + "\n")
        w("end", "【诚实回测】用同一算法组合预测历史各期，与实际开奖比对：\n")
        if bt.get("trials"):
            w("end", f"  回测期数 {bt['trials']}｜平均命中 {bt['avg_hits']:.3f}｜随机期望 {bt['expected']:.3f}\n")
            w("end", f"  命中区间 [{bt['min_hits']}, {bt['max_hits']}]\n")
            edge = bt["avg_hits"] - bt["expected"]
            verdict = "≈ 随机期望，无预测增益" if abs(edge) < 0.4 else ("略高（多为样本噪声）" if edge > 0 else "略低")
            w("end", f"  结论：{verdict}。开奖独立随机，推理仅供复盘。\n")
        else:
            w("end", "  样本不足以回测（需 > 窗口+15 期）。\n")
        self.predict_text.configure(state="disabled")
        self.crawl_status.configure(text=f"已基于 {pred['T']} 期真实数据、{len(pred['enabled'])} 个算法完成推理（复盘用，非真实预测）。", fg=GOLD)

    def _crawl_apply_picks(self):
        if not self._last_prediction:
            messagebox.showinfo("未分析", "请先点击「分析推理」。")
            return
        rec = [x for x in self._last_prediction["recommended"] if x not in self.killed]  # type: ignore
        if not rec:
            messagebox.showinfo("全被杀号", "推荐号全部处于杀号状态，无法写入。")
            return
        self.selected = set(rec)
        self._refresh_pick_ui()
        self.nb.select(self.tab_play)
        self.status.configure(text=f"已写入推荐 {len(rec)} 码到选号区（复盘参考）", fg=GOLD)

    def _crawl_apply_with_kill(self):
        """推荐号一键导入开奖栏：写入投注选号，并把其余号码全部自动设为杀号。"""
        if not self._last_prediction:
            messagebox.showinfo("未分析", "请先点击「分析推理」。")
            return
        rec = sorted(self._last_prediction["recommended"])  # type: ignore
        if len(rec) < KILL_POOL_MIN:
            messagebox.showinfo(
                "推荐号不足",
                f"自动杀号后奖池须至少保留 {KILL_POOL_MIN} 个号码，当前推荐仅 {len(rec)} 个。",
            )
            return
        self.selected = set(rec)
        self.killed = {i for i in range(1, N_POOL + 1) if i not in self.selected}
        self._refresh_pick_ui()
        self.nb.select(self.tab_play)
        self.status.configure(
            text=f"已导入推荐 {len(rec)} 码到开奖栏，并自动杀掉其余 {len(self.killed)} 码。",
            fg=GOLD,
        )


def main():
    app = Happy8App()
    app.mainloop()


if __name__ == "__main__":
    main()
