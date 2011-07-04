"""
    Test configuration descriptions for mira.
"""

import os
from os import path
from glob import glob
import re

from configurations import Isabelle as isabelle


def extract_afp_status(logdata):

    status = dict((session, 'ok') for session in re.findall(r'Testing \[([^\]]+)\]', logdata))

    for match in re.findall(r'The following tests failed:\n([^\n]*)', logdata):
        for session in match.strip().split(' '):
            status[session] = 'FAIL'

    for match in re.findall(r'The following tests were skipped:\n([^\n]*)', logdata):
        for session in match.split(' '):
            status[session] = 'skipped'

    return status


def run_afp_sessions(env, case, paths, dep_paths, playground, fast=False):

    (afp_home, isabelle_home) = paths
    (dep_isabelle,) = dep_paths
    isabelle.prepare_isabelle_repository(isabelle_home, env.settings.contrib, dep_isabelle,
      usedir_options=isabelle.default_usedir_options)
    os.chdir(afp_home)

    # FIXME: guess missing ML_IDENTIFIER for ISABELLE_IMAGE_PATH
    loc_images = glob(dep_isabelle + '/*')
    if len(loc_images) != 1:
        raise Exception('Bad Isabelle image path: %s' % loc_images)
    isabelle_image_path = loc_images[0] + '/'

    fast_flag = ['-f'] if fast else []
    (return_code, log) = env.run_process('admin/testall', '-t',
        path.join(isabelle_home, 'bin', 'isabelle'), *fast_flag,
        ISABELLE_IMAGE_PATH = isabelle_image_path)

    data = {'status': extract_afp_status(log),
      'timing': isabelle.extract_isabelle_run_timing(log) }

    return (return_code == 0, isabelle.extract_isabelle_run_summary(log),
      data, {'log': log}, None)


@configuration(repos = [AFP, Isabelle], deps = [(isabelle.AFP_images, [1])])
def AFP_complete(env, case, paths, dep_paths, playground):
    """Full AFP test"""
    return run_afp_sessions(env, case, paths, dep_paths, playground)

@configuration(repos = [AFP, Isabelle], deps = [(isabelle.AFP_images, [1])])
def AFP_fast(env, case, paths, dep_paths, playground):
    """Full AFP test"""
    return run_afp_sessions(env, case, paths, dep_paths, playground, fast=True)


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
