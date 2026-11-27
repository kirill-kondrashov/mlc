#!/usr/bin/env python3
"""Checks of the raster of the parameter map against a direct computation."""

from __future__ import annotations

import struct
import zlib

import numpy as np

from map_raster import (
    composite,
    coverage,
    decode_png_gray,
    encode_png,
    encode_png_gray,
    rect_pixels,
)


def brute_force(rects: np.ndarray, width: int, height: int) -> np.ndarray:
    out = np.zeros((height, width))
    for x0, y0, x1, y1 in rects:
        x0, x1 = max(x0, 0.0), min(x1, float(width))
        y0, y1 = max(y0, 0.0), min(y1, float(height))
        for j in range(int(np.floor(y0)), int(np.ceil(y1))):
            overlap_y = min(y1, j + 1) - max(y0, j)
            for i in range(int(np.floor(x0)), int(np.ceil(x1))):
                out[j, i] += (min(x1, i + 1) - max(x0, i)) * overlap_y
    return out


def disjoint_rects(rng: np.random.Generator, count: int, width: int, height: int) -> np.ndarray:
    kept: list[np.ndarray] = []
    for _ in range(count):
        x0 = rng.uniform(-3, width + 3)
        y0 = rng.uniform(-3, height + 3)
        rect = np.array([x0, y0, x0 + rng.uniform(0.01, 9), y0 + rng.uniform(0.01, 9)])
        if all(
            rect[2] <= k[0] or k[2] <= rect[0] or rect[3] <= k[1] or k[3] <= rect[1]
            for k in kept
        ):
            kept.append(rect)
    return np.array(kept)


def test_coverage_matches_brute_force() -> None:
    rng = np.random.default_rng(1)
    for width, height in ((40, 30), (17, 53)):
        rects = disjoint_rects(rng, 80, width, height)
        error = np.abs(coverage(rects, width, height) - brute_force(rects, width, height))
        assert error.max() < 1e-9, error.max()


def test_coverage_keeps_the_area_of_tiny_cells() -> None:
    rng = np.random.default_rng(2)
    side = 0.1
    cells = np.unique(rng.integers(0, 4000, size=(5000, 2)), axis=0)
    rects = np.concatenate([cells * side, cells * side + side], axis=1)
    total = coverage(rects, 400, 400).sum()
    assert abs(total - len(rects) * side * side) < 1e-6, total


def test_rect_pixels_flips_the_imaginary_axis() -> None:
    pixels = rect_pixels([(0.0, 0.0, 1.0, 1.0)], (-1.0, 1.0, -1.0, 1.0), (20, 20), 2)
    assert np.allclose(pixels, [[20.0, 0.0, 40.0, 20.0]])


def test_composite_and_png() -> None:
    rects = np.array([[0.0, 0.0, 4.0, 4.0]])
    canvas = composite([(rects, (1.0, 0.0, 0.0), 0.5), (rects, (0.0, 0.0, 1.0), 0.5)], 8, 8)
    assert np.allclose(canvas[0, 0], [0.25, 0.0, 0.5, 0.75])
    assert np.allclose(canvas[7, 7], 0.0)
    png = encode_png(canvas)
    assert png[:8] == b"\x89PNG\r\n\x1a\n"
    width, height = struct.unpack(">II", png[16:24])
    assert (width, height) == (8, 8)
    start = png.index(b"IDAT") + 4
    length = struct.unpack(">I", png[start - 8 : start - 4])[0]
    assert len(zlib.decompress(png[start : start + length])) == 8 * (1 + 4 * 8)


def png_with_filters(image: np.ndarray, kinds: list[int]) -> bytes:
    """An 8-bit grayscale PNG whose row `y` is stored with the PNG filter type `kinds[y]`."""
    height, width = image.shape
    stream = bytearray()
    for y in range(height):
        stream.append(kinds[y])
        for x in range(width):
            left = int(image[y, x - 1]) if x else 0
            up = int(image[y - 1, x]) if y else 0
            upper_left = int(image[y - 1, x - 1]) if x and y else 0
            slope = left + up - upper_left
            nearest = min((abs(slope - v), i, v) for i, v in enumerate((left, up, upper_left)))[2]
            predicted = (0, left, up, (left + up) // 2, nearest)[kinds[y]]
            stream.append((int(image[y, x]) - predicted) & 255)

    def chunk(kind: bytes, data: bytes) -> bytes:
        body = kind + data
        return struct.pack(">I", len(data)) + body + struct.pack(">I", zlib.crc32(body))

    return (
        b"\x89PNG\r\n\x1a\n"
        + chunk(b"IHDR", struct.pack(">IIBBBBB", width, height, 8, 0, 0, 0, 0))
        + chunk(b"IDAT", zlib.compress(bytes(stream)))
        + chunk(b"IEND", b"")
    )


def test_decode_png_gray_reads_every_filter_type() -> None:
    rng = np.random.default_rng(3)
    image = rng.integers(0, 256, size=(9, 13), dtype=np.uint8)
    image[3:6] = 255
    png = png_with_filters(image, [0, 1, 2, 3, 4, 4, 3, 2, 1])
    assert np.array_equal(decode_png_gray(png), image)
    assert np.array_equal(decode_png_gray(encode_png_gray(image)), image)


if __name__ == "__main__":
    for name, function in sorted(globals().items()):
        if name.startswith("test_"):
            function()
            print(f"ok {name}")
