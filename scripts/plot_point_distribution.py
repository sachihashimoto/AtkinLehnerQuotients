#!/usr/bin/env python3
"""Distribution of the number of rational points on X_0^*(N), one row per genus.

Each row is a histogram for one genus: the height of the bar over k is the
fraction of the squarefree levels N of that genus whose curve X_0^*(N) has
exactly k rational cusps and CM points.  Bars rise from the row's baseline.

Usage (from the repository root):

    python3 scripts/plot_point_distribution.py [--counts] [--no-guides] [DATA [OUTPUT]]

--counts      print the number of curves above each bar
--no-guides   leave out the dotted 10% and 20% lines and the right-hand axis

DATA defaults to data/x0star_point_counts.txt, which has one line per level:
    <genus> <N> <points> <disc>:<count> ...
Only the first and third fields are used here.  Regenerate the file with
scripts/make_point_count_table.m.
OUTPUT defaults to outputs/x0star_distribution_profiles.pdf.

Needs matplotlib.
"""
import os
import sys
from collections import Counter

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt

args = [a for a in sys.argv[1:] if not a.startswith("--")]
COUNTS = "--counts" in sys.argv
GUIDES = "--no-guides" not in sys.argv
DATA = args[0] if len(args) > 0 else "data/x0star_point_counts.txt"
OUTPUT = args[1] if len(args) > 1 else "outputs/x0star_distribution_profiles.pdf"

by_genus = {}
for line in open(DATA):
    parts = line.split()
    if parts:
        by_genus.setdefault(int(parts[0]), []).append(int(parts[2]))
rows = sorted(by_genus.items())

kmin = min(min(cs) for _, cs in rows)
kmax = max(max(cs) for _, cs in rows)
ks = list(range(kmin, kmax + 1))

# One row per unit of y.  The tallest bar in the figure takes FILL of a row, so
# no histogram reaches the baseline of the row above it.
# With counts printed above the bars the tallest one needs room for its label.
FILL = 0.68 if COUNTS else 0.80
peak = max(max(Counter(cs).values()) / len(cs) for _, cs in rows)
scale = FILL / peak                      # y units per unit of fraction

fig, ax = plt.subplots(figsize=(7.2, 8.8))

for k in ks:                             # very faint vertical guides
    ax.axvline(k, color="0.90", lw=0.5, zorder=0)

# Reference heights, as fractions of the curves of one genus.  They are drawn
# as dotted lines across every row and labelled on the right-hand axis.
LEVELS = (0.10, 0.20)
scale_ticks, scale_labels = [], []

labels, ticks = [], []
for i, (g, cs) in enumerate(rows):
    base = -i                            # genus increases down the page
    n = len(cs)
    count = Counter(cs)
    # Step outline: each bar spans [k - 0.5, k + 0.5].
    xs = [kmin - 0.5]
    ys = [base]
    for k in ks:
        top = base + scale * count.get(k, 0) / n
        xs += [k - 0.5, k + 0.5]
        ys += [top, top]
    xs.append(kmax + 0.5)
    ys.append(base)
    ax.fill_between(xs, base, ys, color="0.86", lw=0, zorder=1)
    for k in ks if COUNTS else []:       # number of curves above each bar
        if count.get(k, 0):
            ax.text(k, base + scale * count[k] / n + 0.03, str(count[k]),
                    ha="center", va="bottom", fontsize=6, color="0.35", zorder=4)
    for level in LEVELS if GUIDES else []:   # the same reference heights in every row
        y = base + scale * level
        ax.plot([kmin - 0.5, kmax + 0.5], [y, y], color="0.45", lw=0.5,
                dashes=(1, 2.5), zorder=2)
        scale_ticks.append(y)
        scale_labels.append("%d%%" % round(100 * level))
    ax.plot([kmin - 0.5, kmax + 0.5], [base, base], color="0.55", lw=0.5, zorder=2)
    # Outline each run of non-empty bars on its own, so that empty stretches
    # show only the thin baseline.
    run = []
    for k in ks + [None]:
        if k is not None and count.get(k, 0):
            run.append(k)
            continue
        if run:
            ox, oy = [run[0] - 0.5], [base]
            for j in run:
                top = base + scale * count[j] / n
                ox += [j - 0.5, j + 0.5]
                oy += [top, top]
            ox.append(run[-1] + 0.5)
            oy.append(base)
            ax.plot(ox, oy, color="black", lw=0.8, zorder=3, solid_joinstyle="miter")
            run = []
    ticks.append(base)
    labels.append(r"$g = %d$  ($n = %d$)" % (g, n))

ax.set_xlim(kmin - 0.7, kmax + 0.7)
for side in ("top", "right", "left"):    # no box: the rows carry the structure
    ax.spines[side].set_visible(False)
ax.set_ylim(-(len(rows) - 1) - 0.25, 1.0)
ax.set_xticks(ks)
ax.set_yticks(ticks)
ax.set_yticklabels(labels, fontsize=9)
ax.tick_params(axis="y", length=0)
ax.set_xlabel(r"Number of rational points on $X_0^*(N)$", fontsize=11)
ax.set_ylabel("Genus and sample size", fontsize=11)

# Right-hand axis: the percentage scale, repeated for each row.
if GUIDES:
    right = ax.twinx()
    for side in ("top", "right", "left"):
        right.spines[side].set_visible(False)
    right.set_ylim(ax.get_ylim())
    right.set_yticks(scale_ticks)
    right.set_yticklabels(scale_labels, fontsize=6, color="0.35")
    right.tick_params(axis="y", length=0, pad=2)
    right.set_ylabel("Share of the curves of that genus", fontsize=11)

fig.tight_layout()
if os.path.dirname(OUTPUT):
    os.makedirs(os.path.dirname(OUTPUT), exist_ok=True)
fig.savefig(OUTPUT)
print("%s: genus %d-%d, %d curves, tallest bar %.1f%%"
      % (OUTPUT, rows[0][0], rows[-1][0], sum(len(cs) for _, cs in rows), 100 * peak))
