from __future__ import print_function
from sys import stderr
from termcolor import colored

from config import options

def debug(message, indent=0, title=""):
    if options.enable_debug:
        if isinstance(message, list):
            debug(title + ": [" if title else "[", indent)
            for line in message:
                debug(line, indent + 2)
            debug("]", indent)
        elif isinstance(message, dict):
            debug(title + ": {" if title else "{", indent)
            for key, value in message.items():
                debug(u"{0} -> {1}".format(key, value), indent + 2)
            debug("}", indent)
        else:
            if title:
                print(u"Debug: {0}{1}: {2}".format(' ' * indent, title, message), file=stderr)
            else:
                print(u"Debug: {0}{1}".format(' ' * indent, message), file=stderr)

def warn(message):
    if options.enable_warnings:
        print(colored(u"Warning: {0}".format(message), 'yellow', attrs=['bold']), file=stderr)

def error(message, exception=None, abort=False):
    print(colored(u"Error: {0}".format(message), 'red', attrs=['bold']), file=stderr)
    if exception:
        error("*** exception message:")
        error(u"*** {0!s} {1!s}".format(exception, type(exception)))
    if abort:
        error("Fatal. Aborting")
        exit(1)

def success(message):
    print(colored("Success: {0}".format(message), 'green'), file=stderr)
