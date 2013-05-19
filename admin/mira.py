"""
    Test configuration descriptions for mira.
"""

import os
from os import path
from glob import glob
import re

from configurations import Isabelle as isabelle
from mira import misc



afp_settings='''
ML_OPTIONS="-H 1000 --gcthreads 4"

ISABELLE_BUILD_OPTIONS="threads=4 parallel_proofs=2"
'''

afp_jobs = "6" if 'lxbroy10' in misc.hostnames() else "2"

@configuration(repos = [Isabelle, AFP], deps = [])
def AFP(*args):
    """Main AFP test, excluding very large sessions"""

    afp_thys = path.join(args[2][1], 'thys')
    return isabelle.isabelle_build(*(args + ("-j", afp_jobs, "-d", afp_thys, "-g", "AFP")), more_settings=afp_settings)

@configuration(repos = [Isabelle, AFP], deps = [(AFP, [0, 1])])
def AFP_big(*args):
    """Large Sessions from AFP"""

    afp_thys = path.join(args[2][1], 'thys')
    return isabelle.isabelle_build(*(args + ("-j", afp_jobs, "-d", afp_thys, "-g", "AFP_big")), more_settings=afp_settings)


# AFP-based Judgement Day configurations

@configuration(repos = [Isabelle, AFP], deps = [(isabelle.HOL, [0])])
def JD_Arrow(*args):
    """Judgement Day regression suite Arrow"""
    return isabelle.judgement_day('AFP/thys/ArrowImpossibilityGS/Thys', 'Arrow_Order', 'prover_timeout=10', *args)

@configuration(repos = [Isabelle, AFP], deps = [(isabelle.HOL, [0])])
def JD_FFT(*args):
    """Judgement Day regression suite FFT"""
    return isabelle.judgement_day('AFP/thys/FFT', 'FFT', 'prover_timeout=10', *args)

@configuration(repos = [Isabelle, AFP], deps = [(isabelle.HOL, [0])])
def JD_Jinja(*args):
    """Judgement Day regression suite Jinja"""
    return isabelle.judgement_day('AFP/thys/Jinja/J', 'TypeSafe', 'prover_timeout=10', *args)

@configuration(repos = [Isabelle, AFP], deps = [(isabelle.HOL, [0])])
def JD_QE(*args):
    """Judgement Day regression suite QE"""
    return isabelle.judgement_day('AFP/thys/LinearQuantifierElim/Thys', 'QEpres', 'prover_timeout=10', *args)

@configuration(repos = [Isabelle, AFP], deps = [(isabelle.HOL, [0])])
def JD_S2S(*args):
    """Judgement Day regression suite S2S"""
    return isabelle.judgement_day('AFP/thys/SumSquares', 'TwoSquares', 'prover_timeout=10', *args)
