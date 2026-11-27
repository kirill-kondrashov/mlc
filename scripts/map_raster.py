"""Raster rendering of the rectangle layers of the parameter map.

The map of M paints about 600 000 axis-parallel rectangles in a dozen translucent layers.
As vector paths they weigh 18 MB, and the browsers that rasterize such a path on the GPU
can draw nothing at all. The layers are composited here, with the exact area coverage of
every pixel, into one PNG that the map embeds as an image.
"""

from __future__ import annotations

import base64
import struct
import zlib

import numpy as np


def hex_rgb(color: str) -> tuple[float, float, float]:
    """The channels, in [0, 1], of a color `#rrggbb`."""
    value = color.lstrip("#")
    return tuple(int(value[i : i + 2], 16) / 255.0 for i in (0, 2, 4))  # type: ignore[return-value]


def rect_pixels(
    rects: list[tuple[float, float, float, float]],
    window: tuple[float, float, float, float],
    grid: tuple[int, int],
    scale: int,
) -> np.ndarray:
    """Rectangles `(x0, y0, x1, y1)` of the parameter plane as pixels of the raster.

    The raster shows `window = (xmin, xmax, ymin, ymax)` in `grid * scale` pixels, with the
    imaginary axis pointing up in the plane and down in the pixels.
    """
    data = np.asarray(rects, dtype=np.float64).reshape(-1, 4)
    xmin, xmax, ymin, ymax = window
    scale_x = grid[0] * scale / (xmax - xmin)
    scale_y = grid[1] * scale / (ymax - ymin)
    return np.stack(
        [
            (data[:, 0] - xmin) * scale_x,
            (ymax - data[:, 3]) * scale_y,
            (data[:, 2] - xmin) * scale_x,
            (ymax - data[:, 1]) * scale_y,
        ],
        axis=1,
    )


def coverage(rects: np.ndarray, width: int, height: int) -> np.ndarray:
    """The fraction of every pixel covered by the union of disjoint rectangles.

    `rects` has one row `(x0, y0, x1, y1)` per rectangle, in pixel units, with `y` downward.
    A rectangle covers the pixel `(i, j)` by `ox(i) * oy(j)`, where `ox(i) = A(i + 1) - A(i)`,
    `A(u) = (u - x0)+ - (u - x1)+` and `oy` is the same for `y`. The sum over the rectangles of
    `A(u) B(v)` is a combination of `(u - a)+ (v - b)+`, and for integer `u`, `v` this is
    `(u v - b u - a v + a b)` after the corner `(ceil a, ceil b)`. Four arrays of corner
    weights, summed over the quadrants, give it for all rectangles in one pass.
    """
    x0 = np.clip(rects[:, 0], 0.0, width)
    x1 = np.clip(rects[:, 2], 0.0, width)
    y0 = np.clip(rects[:, 1], 0.0, height)
    y1 = np.clip(rects[:, 3], 0.0, height)
    keep = (x1 > x0) & (y1 > y0)
    x0, x1, y0, y1 = x0[keep], x1[keep], y0[keep], y1[keep]
    size = (width + 1) * (height + 1)
    seeds = [np.zeros(size) for _ in range(4)]
    for a, sa in ((x0, 1.0), (x1, -1.0)):
        for b, sb in ((y0, 1.0), (y1, -1.0)):
            sign = sa * sb
            index = np.ceil(b).astype(np.int64) * (width + 1) + np.ceil(a).astype(np.int64)
            ones = np.full(len(a), sign)
            seeds[0] += np.bincount(index, weights=ones, minlength=size)
            seeds[1] += np.bincount(index, weights=ones * b, minlength=size)
            seeds[2] += np.bincount(index, weights=ones * a, minlength=size)
            seeds[3] += np.bincount(index, weights=ones * a * b, minlength=size)
    shape = (height + 1, width + 1)
    u = np.arange(width + 1, dtype=np.float64)[None, :]
    v = np.arange(height + 1, dtype=np.float64)[:, None]

    def quadrant_sum(seed: np.ndarray) -> np.ndarray:
        return np.cumsum(np.cumsum(seed.reshape(shape), axis=0), axis=1)

    total = quadrant_sum(seeds[0]) * u
    total *= v
    total -= quadrant_sum(seeds[1]) * u
    total -= quadrant_sum(seeds[2]) * v
    total += quadrant_sum(seeds[3])
    return np.clip(
        total[1:, 1:] - total[1:, :-1] - total[:-1, 1:] + total[:-1, :-1], 0.0, 1.0
    )


def composite(
    layers: list[tuple[np.ndarray, tuple[float, float, float], float]],
    width: int,
    height: int,
    canvas: np.ndarray | None = None,
) -> np.ndarray:
    """Paint translucent layers, in order, on a premultiplied RGBA float canvas.

    A layer is `(rects, rgb, opacity)`: the rectangles, their color and their opacity.
    """
    if canvas is None:
        canvas = np.zeros((height, width, 4), dtype=np.float32)
    for rects, rgb, opacity in layers:
        alpha = (opacity * coverage(rects, width, height)).astype(np.float32)[..., None]
        canvas *= 1.0 - alpha
        canvas[..., :3] += alpha * np.asarray(rgb, dtype=np.float32)
        canvas[..., 3:] += alpha
    return canvas


def encode_png(canvas: np.ndarray) -> bytes:
    """A PNG (RGBA, 8 bit) of a premultiplied RGBA float canvas."""
    height, width, _ = canvas.shape
    alpha = canvas[..., 3:]
    straight = np.divide(canvas[..., :3], alpha, out=np.zeros_like(canvas[..., :3]), where=alpha > 0)
    raw = np.empty((height, width, 4), dtype=np.uint8)
    raw[..., :3] = np.rint(np.clip(straight, 0.0, 1.0) * 255.0)
    raw[..., 3] = np.rint(np.clip(alpha[..., 0], 0.0, 1.0) * 255.0)
    rows = raw.reshape(height, width * 4)
    # Filter type 2 (Up): every row is stored as its difference from the row above.
    filtered = np.empty((height, width * 4 + 1), dtype=np.uint8)
    filtered[:, 0] = 2
    filtered[0, 1:] = rows[0]
    filtered[1:, 1:] = rows[1:] - rows[:-1]

    def chunk(kind: bytes, data: bytes) -> bytes:
        body = kind + data
        return struct.pack(">I", len(data)) + body + struct.pack(">I", zlib.crc32(body))

    return (
        b"\x89PNG\r\n\x1a\n"
        + chunk(b"IHDR", struct.pack(">IIBBBBB", width, height, 8, 6, 0, 0, 0))
        + chunk(b"IDAT", zlib.compress(filtered.tobytes(), 9))
        + chunk(b"IEND", b"")
    )


def png_data_uri(png: bytes) -> str:
    return "data:image/png;base64," + base64.b64encode(png).decode("ascii")
