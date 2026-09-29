"""Checks for suite selection and comparison gates; no benchmark timings."""
from pathlib import Path
import runpy
import unittest

driver = runpy.run_path(str(Path(__file__).with_name("bench-fields.py")))


class Suites(unittest.TestCase):
    def test_all_is_union(self):
        small = driver["selection"]("small-prime")[2]
        large = driver["selection"]("large-prime")[2]
        self.assertEqual(len(small), 18)
        self.assertEqual(len(large), 2)
        self.assertEqual(driver["selection"]("all")[2], small | large)

    def test_reject_missing_duplicate_or_unexpected_cases(self):
        expected = driver["selection"]("large-prime")[2]
        rows = [{"group_key": group, "mode": mode} for group, mode in expected]
        self.assertEqual(driver["indexed"](rows, expected).keys(), expected)
        for invalid in [rows[:-1], rows + [rows[0]],
                        rows + [{"group_key": "unknown", "mode": "latency"}]]:
            with self.assertRaises(ValueError):
                driver["indexed"](invalid, expected)

    def test_reject_wrong_digest_or_work_count(self):
        lean = {("fields-bn254-mul", "latency"): {"checksum": 7, "work_units": 320}}
        for prop in ("checksum", "work_units"):
            rust = {key: dict(row) for key, row in lean.items()}
            next(iter(rust.values()))[prop] += 1
            with self.assertRaises(ValueError):
                driver["compare"](lean, rust)


if __name__ == "__main__":
    unittest.main()
