"""Tests for measure_plain_text.py. Run: python -B test_measure_plain_text.py"""
import json
import os
import tempfile
import unittest

import measure_plain_text as m


def poly(variables, terms):
    handle = tempfile.NamedTemporaryFile("w", suffix=".json", delete=False, encoding="utf-8")
    json.dump({"variables": variables,
               "terms": [{"monomial": mono, "coefficient": coeff} for mono, coeff in terms]}, handle)
    handle.close()
    return handle.name


class PlainText(unittest.TestCase):
    def render(self, variables, terms):
        path = poly(variables, terms)
        try:
            return m.render(m.load_terms(path)[1])
        finally:
            os.unlink(path)

    def test_documented_example(self):
        text = self.render(250, [([2, 250], "1"), ([1, 1, 1, 1], "1"), ([], "17"), ([47, 1, 1], "-2")])
        self.assertEqual(text, "17+x1^4-2*x1^2*x47+x2*x250")

    def test_unit_coefficients_and_leading_sign(self):
        self.assertEqual(self.render(3, [([1], "-1"), ([2], "1")]), "-x1+x2")
        self.assertEqual(self.render(3, [([], "-1"), ([3], "1")]), "-1+x3")
        self.assertEqual(self.render(3, [([], "1")]), "1")

    def test_like_terms_combine_and_zero_terms_vanish(self):
        self.assertEqual(self.render(2, [([1, 2], "3"), ([2, 1], "-3"), ([1], "5")]), "5*x1")

    def test_order_is_by_index_tuple(self):
        self.assertEqual(self.render(12, [([10], "1"), ([2], "1"), ([1, 12], "1"), ([1, 2], "1")]),
                         "x1*x2+x1*x12+x2+x10")

    def test_rejects_parameters_bad_coefficients_and_bad_indices(self):
        for terms in ([{"monomial": [1], "coefficient": "1", "parameterPower": 1}],
                      [{"monomial": [1], "coefficient": "1e3"}],
                      [{"monomial": [1], "coefficient": "007"}],
                      [{"monomial": [1], "coefficient": 5}],
                      [{"monomial": [4], "coefficient": "1"}],
                      [{"monomial": [0], "coefficient": "1"}],
                      [{"monomial": [1], "coefficient": "0"}]):
            handle = tempfile.NamedTemporaryFile("w", suffix=".json", delete=False, encoding="utf-8")
            json.dump({"variables": 3, "terms": terms}, handle)
            handle.close()
            try:
                with self.assertRaises(ValueError):
                    m.load_terms(handle.name)
            finally:
                os.unlink(handle.name)

    def test_limit_is_strict(self):
        path = poly(1, [([], "1" + "0" * 99_999)])  # exactly 100,000 bytes
        try:
            self.assertEqual(m.main([path]), 1)
        finally:
            os.unlink(path)
        path = poly(1, [([], "1" + "0" * 99_998)])  # 99,999 bytes
        try:
            self.assertEqual(m.main([path]), 0)
        finally:
            os.unlink(path)


if __name__ == "__main__":
    unittest.main()
