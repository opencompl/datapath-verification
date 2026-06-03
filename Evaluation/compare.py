import os
import re

import matplotlib.pyplot as plt

OUT_DIR = "compare_out"
OPT_DIR = os.path.join(OUT_DIR, "optimized")
os.makedirs(OPT_DIR, exist_ok=True)

COMPARISON_FILE = os.path.join(
    os.path.dirname(os.path.dirname(os.path.abspath(__file__))),
    "comparison.txt",
)

# Map theorem-name prefix -> series key.
# mulChain_*    -> csa     (carry-save adder tree)
# mulChain_opt_*-> csa_opt (optimized CSA)
# mul_comm_*    -> bb      (bitblaster / schoolbook fallback)
SERIES = ("csa", "csa_opt", "bb")

THEOREM_RE = re.compile(
    r"^\[Elab\.command\]\s+\[([0-9.]+)\]\s+theorem\s+(\S+)"
)
SAT_RE = re.compile(
    r"\[Meta\.Tactic\.sat\]\s+\[([0-9.]+)\]\s+Running SAT solver"
)
BIT_RE = re.compile(r"_(\d+)bit\b")


def classify(theorem_name: str) -> str | None:
    """Return series key for a theorem name, or None to skip."""
    if theorem_name.startswith("mulChain_opt"):
        return "csa_opt"
    if theorem_name.startswith("mulChain_"):
        return "csa"
    if theorem_name.startswith("mul_comm"):
        return "bb"
    return None


def parse(path: str) -> dict[str, dict[int, tuple[float, float]]]:
    """Parse the trace file.

    Returns: {series_key: {bit_width: (total_time, sat_time)}}.
    """
    out: dict[str, dict[int, tuple[float, float]]] = {k: {} for k in SERIES}

    with open(path) as f:
        lines = f.readlines()

    i = 0
    n = len(lines)
    while i < n:
        m = THEOREM_RE.match(lines[i])
        if not m:
            i += 1
            continue
        total = float(m.group(1))
        name = m.group(2)
        bit_match = BIT_RE.search(name)
        series = classify(name)
        i += 1
        # Find SAT-solver time in the block before next theorem header.
        sat_time = None
        while i < n and not THEOREM_RE.match(lines[i]):
            sm = SAT_RE.search(lines[i])
            if sm and sat_time is None:
                sat_time = float(sm.group(1))
            i += 1
        if series is None or bit_match is None or sat_time is None:
            continue
        width = int(bit_match.group(1))
        out[series][width] = (total, sat_time)

    return out


def aligned(parsed: dict[str, dict[int, tuple[float, float]]]):
    """Compute the common bit-widths and aligned series lists."""
    widths_by_series = [set(parsed[k].keys()) for k in SERIES if parsed[k]]
    if not widths_by_series:
        raise RuntimeError("No theorem data parsed.")
    common = sorted(set.intersection(*widths_by_series))
    series_data = {}
    for k in SERIES:
        if not parsed[k]:
            series_data[k] = {"total": [], "sat": [], "widths": []}
            continue
        widths_k = sorted(parsed[k].keys())
        series_data[k] = {
            "widths": widths_k,
            "total": [parsed[k][w][0] for w in widths_k],
            "sat": [parsed[k][w][1] for w in widths_k],
        }
    return common, series_data


PARSED = parse(COMPARISON_FILE)
COMMON_WIDTHS, SERIES_DATA = aligned(PARSED)


def series_lists(key: str):
    """Return (widths, total, sat) for a series at all widths it has."""
    d = PARSED[key]
    widths = sorted(d.keys())
    total = [d[w][0] for w in widths]
    sat = [d[w][1] for w in widths]
    return widths, total, sat


def pair_lists(key_a: str, key_b: str):
    """Return aligned (widths, a_total, a_sat, b_total, b_sat) at widths shared by both series."""
    common = sorted(set(PARSED[key_a]) & set(PARSED[key_b]))
    a_t = [PARSED[key_a][w][0] for w in common]
    a_s = [PARSED[key_a][w][1] for w in common]
    b_t = [PARSED[key_b][w][0] for w in common]
    b_s = [PARSED[key_b][w][1] for w in common]
    return common, a_t, a_s, b_t, b_s


# Pair-aligned (csa vs bb) lists used by the bitblaster-vs-CSA plots.
widths, csa_total, csa_sat, bitblaster_total, bitblaster_sat = pair_lists("csa", "bb")

_widths_opt, csa_opt_total, csa_opt_sat = (
    sorted(PARSED["csa_opt"].keys()),
    [PARSED["csa_opt"][w][0] for w in sorted(PARSED["csa_opt"].keys())],
    [PARSED["csa_opt"][w][1] for w in sorted(PARSED["csa_opt"].keys())],
)


def deltas(a, b):
    return [bi - ai for ai, bi in zip(a, b)]


def _style(ax, title, ylabel, xs):
    ax.axhline(0, color="black", linewidth=0.8)
    ax.set_xticks(xs)
    ax.set_xlabel("bit-width")
    ax.set_ylabel(ylabel)
    ax.set_title(title)
    ax.legend()
    ax.grid(True, linestyle=":", alpha=0.5)


def plot_deltas():
    if not widths:
        return
    d_total = deltas(bitblaster_total, csa_total)
    d_sat = deltas(bitblaster_sat, csa_sat)

    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(12, 5))
    ax1.plot(widths, d_total, marker="o", color="C0",
             label="bitblaster - CSA")
    _style(ax1, "delta full bv_decide", "time difference (s)", widths)

    ax2.plot(widths, d_sat, marker="s", color="C1",
             label="bitblaster - CSA")
    _style(ax2, "delta SAT-only", "time difference (s)", widths)

    fig.suptitle("bv_decide: bitblaster vs CSA (deltas)")
    fig.tight_layout()
    fig.savefig(os.path.join(OUT_DIR, "compare_deltas.png"), dpi=150)


def plot_absolute():
    fig, axes = plt.subplots(2, 2, figsize=(12, 8))
    (ax_ct, ax_bt), (ax_cs, ax_bs) = axes

    cw, ct, cs = series_lists("csa")
    bw, bt, bs = series_lists("bb")

    if ct:
        ax_ct.plot(cw, ct, marker="o", color="C0", label="CSA")
        _style(ax_ct, "CSA - full bv_decide", "time (s)", cw)
    if bt:
        ax_bt.plot(bw, bt, marker="o", color="C2", label="bitblaster")
        _style(ax_bt, "bitblaster - full bv_decide", "time (s)", bw)
    if cs:
        ax_cs.plot(cw, cs, marker="s", color="C0", label="CSA")
        _style(ax_cs, "CSA - SAT-only", "time (s)", cw)
    if bs:
        ax_bs.plot(bw, bs, marker="s", color="C2", label="bitblaster")
        _style(ax_bs, "bitblaster - SAT-only", "time (s)", bw)

    fig.suptitle("bv_decide: absolute timings")
    fig.tight_layout()
    fig.savefig(os.path.join(OUT_DIR, "compare_absolute.png"), dpi=150)


def plot_relative():
    if not widths:
        return
    rel_total = [abs(b - a) / max(a, b) * 100
                 for a, b in zip(csa_total, bitblaster_total)]
    rel_sat = [abs(b - a) / max(a, b) * 100
               for a, b in zip(csa_sat, bitblaster_sat)]

    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(12, 5))
    ax1.plot(widths, rel_total, marker="o", color="C0",
             label="|bitblaster - CSA| / max")
    _style(ax1, "delta full bv_decide (relative)", "time difference (%)", widths)

    ax2.plot(widths, rel_sat, marker="s", color="C1",
             label="|bitblaster - CSA| / max")
    _style(ax2, "delta SAT-only (relative)", "time difference (%)", widths)

    fig.suptitle("bv_decide: bitblaster vs CSA")
    fig.tight_layout()
    fig.savefig(os.path.join(OUT_DIR, "compare_relative.png"), dpi=150)


def _rel(a, b):
    return [abs(bi - ai) / max(ai, bi) * 100 for ai, bi in zip(a, b)]


def _intersect(*series_keys):
    sets = [set(PARSED[k].keys()) for k in series_keys if PARSED[k]]
    if len(sets) != len(series_keys):
        return []
    return sorted(set.intersection(*sets))


def plot_optimized_absolute():
    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(12, 5))

    cw, ct, cs = series_lists("csa")
    bw, bt, bs = series_lists("bb")
    ow = sorted(PARSED["csa_opt"].keys())
    ot = [PARSED["csa_opt"][w][0] for w in ow]
    os_ = [PARSED["csa_opt"][w][1] for w in ow]

    all_widths = sorted(set(cw) | set(bw) | set(ow))
    if ct:
        ax1.plot(cw, ct, marker="o", color="C0", label="CSA")
    if bt:
        ax1.plot(bw, bt, marker="o", color="C2", label="bitblaster")
    if ot:
        ax1.plot(ow, ot, marker="o", color="C3", label="CSA (optimized)")
    _style(ax1, "full bv_decide", "time (s)", all_widths)

    if cs:
        ax2.plot(cw, cs, marker="s", color="C0", label="CSA")
    if bs:
        ax2.plot(bw, bs, marker="s", color="C2", label="bitblaster")
    if os_:
        ax2.plot(ow, os_, marker="s", color="C3", label="CSA (optimized)")
    _style(ax2, "SAT-only", "time (s)", all_widths)

    fig.suptitle("bv_decide: CSA vs bitblaster vs optimized CSA")
    fig.tight_layout()
    fig.savefig(os.path.join(OPT_DIR, "compare_optimized_absolute.png"), dpi=150)


def plot_optimized_deltas():
    common = _intersect("csa", "csa_opt", "bb")
    if not common:
        return
    csa_t = [PARSED["csa"][w][0] for w in common]
    csa_s = [PARSED["csa"][w][1] for w in common]
    bb_t = [PARSED["bb"][w][0] for w in common]
    bb_s = [PARSED["bb"][w][1] for w in common]
    opt_t = [PARSED["csa_opt"][w][0] for w in common]
    opt_s = [PARSED["csa_opt"][w][1] for w in common]

    d_total_csa = deltas(csa_t, opt_t)
    d_total_bb = deltas(bb_t, opt_t)
    d_sat_csa = deltas(csa_s, opt_s)
    d_sat_bb = deltas(bb_s, opt_s)

    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(12, 5))
    ax1.plot(common, d_total_csa, marker="o", color="C0",
             label="optimized - CSA")
    ax1.plot(common, d_total_bb, marker="o", color="C2",
             label="optimized - bitblaster")
    _style(ax1, "delta full bv_decide", "time difference (s)", common)

    ax2.plot(common, d_sat_csa, marker="s", color="C0",
             label="optimized - CSA")
    ax2.plot(common, d_sat_bb, marker="s", color="C2",
             label="optimized - bitblaster")
    _style(ax2, "delta SAT-only", "time difference (s)", common)

    fig.suptitle("bv_decide: optimized CSA vs CSA / bitblaster (deltas)")
    fig.tight_layout()
    fig.savefig(os.path.join(OPT_DIR, "compare_optimized_deltas.png"), dpi=150)


def plot_optimized_relative():
    common = _intersect("csa", "csa_opt", "bb")
    if not common:
        return
    csa_t = [PARSED["csa"][w][0] for w in common]
    csa_s = [PARSED["csa"][w][1] for w in common]
    bb_t = [PARSED["bb"][w][0] for w in common]
    bb_s = [PARSED["bb"][w][1] for w in common]
    opt_t = [PARSED["csa_opt"][w][0] for w in common]
    opt_s = [PARSED["csa_opt"][w][1] for w in common]

    rel_total_csa = _rel(csa_t, opt_t)
    rel_total_bb = _rel(bb_t, opt_t)
    rel_sat_csa = _rel(csa_s, opt_s)
    rel_sat_bb = _rel(bb_s, opt_s)

    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(12, 5))
    ax1.plot(common, rel_total_csa, marker="o", color="C0",
             label="|optimized - CSA| / max")
    ax1.plot(common, rel_total_bb, marker="o", color="C2",
             label="|optimized - bitblaster| / max")
    _style(ax1, "delta full bv_decide (relative)", "time difference (%)", common)

    ax2.plot(common, rel_sat_csa, marker="s", color="C0",
             label="|optimized - CSA| / max")
    ax2.plot(common, rel_sat_bb, marker="s", color="C2",
             label="|optimized - bitblaster| / max")
    _style(ax2, "delta SAT-only (relative)", "time difference (%)", common)

    fig.suptitle("bv_decide: optimized CSA vs CSA / bitblaster (relative)")
    fig.tight_layout()
    fig.savefig(os.path.join(OPT_DIR, "compare_optimized_relative.png"), dpi=150)


def main():
    print("Parsed series (bit-width -> (total, sat)):")
    for k in SERIES:
        print(f"  {k}: {dict(sorted(PARSED[k].items()))}")

    plot_deltas()
    plot_absolute()
    plot_relative()
    plot_optimized_absolute()
    plot_optimized_deltas()
    plot_optimized_relative()
    plt.show()


if __name__ == "__main__":
    main()
