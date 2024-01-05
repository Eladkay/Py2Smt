import unittest

from analysis import GraphIntervalAnalysis
from py2smt import Py2Smt
from .smt_test_case import SmtTestCase


class AnalyzedClass:
    def interval1(self) -> int:
        a = 50
        if a > 10:
            a = 20
        return a


class Py2SmtAnalysisTests(SmtTestCase):
    def test_interval1(self):
        system = Py2Smt([AnalyzedClass])
        cfg = system.get_entry_by_name("interval1").cfg
        analysis = GraphIntervalAnalysis(cfg)
        analysis.iterate()
        self.assertEqual(analysis.results[cfg.end]["a"], (20, 20))


if __name__ == '__main__':
    unittest.main()
