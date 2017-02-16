#!/usr/bin/env python

##
## Dependencies: Python 2.7 or Python 3.5
##
## This script reads a metadata file and generates the topics.shtml,
## index.shtml and the entry pages on isa-afp.org.
##
## For meta data documentation see `metadata/README`
## For adding new entries see `doc/editors/new-entry-checkin.html`
##

# Cross-python compatibility
from __future__ import print_function
try:
	import configparser
except ImportError:
	from six.moves import configparser

from collections import OrderedDict
from optparse import OptionParser
from sys import argv, stderr
from functools import partial
from operator import itemgetter
import codecs
import os
import re
from termcolor import colored
import json

# modules
from config import *
from metadata import *
from terminal import *
import templates
import afpstats



class Stats(object):
	def __init__(self):
		self.tpls = 0
		self.failed_tpls = 0
		self.gens = 0
		self.failed_gens = 0

	def __str__(self):
		failed_tpl_str = "({0!s} failed)".format(self.failed_tpls) if self.failed_tpls > 0 else ""
		failed_gen_str = "({0!s} failed)".format(self.failed_gens) if self.failed_gens > 0 else ""

		success_tpl_str = "Successfully read {0!s} template(s)".format(self.tpls - self.failed_tpls)
		success_gen_str = "Successfully written {0!s} file(s)".format(self.gens - self.failed_gens)

		return "{0} {1}\n{2} {3}".format(
			colored(success_tpl_str, 'green', attrs=['bold']),
			colored(failed_tpl_str, 'red', attrs=['bold']),
			colored(success_gen_str, 'green', attrs=['bold']),
			colored(failed_gen_str, 'red', attrs=['bold'])
		)

# performs a 'diff' between metadata and the actual filesystem contents
def check_fs(meta_entries, directory):
	fs_entries = set(e for e in os.listdir(directory) if os.path.isdir(os.path.join(directory, e)))
	meta_entries = set(k for k, _ in meta_entries.items())
	# check for entries not existing in filesystem
	for fs_missing in meta_entries - fs_entries:
		print(colored(u"Check: In metadata: entry {0} doesn't exist in filesystem".format(fs_missing), 'yellow', attrs=['bold']), file=stderr)
	for meta_missing in fs_entries - meta_entries:
		print(colored(u"Check: In filesystem: entry {0} doesn't exist in metadata".format(meta_missing), 'yellow', attrs=['bold']), file=stderr)
	return len(fs_entries ^ meta_entries)

# takes the 'raw' data from metadata file as input and performs:
# * checking of data against attribute_schema
# * defaults for missing keys
# * elimination of extraneous keys
# * splitting at ',' if an array is requested
def validate(entry, attributes):
	sane_attributes = {}
	missing_keys = []
	processed_keys = set()
	for key, (split, processor, default) in attribute_schema.items():
		if processor is None:
			processor = lambda str, **kwargs: str
		if key.endswith("*"):
			shortkey = key[:len(key)-1]
			result = OrderedDict()
			process = partial(processor, entry = entry, shortkey = shortkey)
			for appkey, str in attributes.items():
				if appkey.startswith(shortkey + "-"):
					processed_keys.add(appkey)
					app = appkey[len(shortkey) + 1:]
					if not split:
						result[app] = process(str.strip(), appendix = app)
					else:
						result[app] = [process(s.strip(), appendix = app) for s in str.split(',')]
			sane_attributes[shortkey] = result
		else:
			process = partial(processor, entry = entry, key = key)
			if default == None and key not in attributes:
				missing_keys.append(key)
				sane_attributes[key] = process("") if not split else []
			else:
				value = attributes[key] if key in attributes else default
				processed_keys.add(key)
				if not split:
					sane_attributes[key] = process(value)
				else:
					sane_attributes[key] = [process(s.strip()) for s in value.split(',')]
	if missing_keys:
		warn(u"In entry {0}: missing key(s) {1!s}".format(entry, missing_keys))

	extraneous_keys = set(attributes.keys()) - processed_keys
	if extraneous_keys:
		warn(u"In entry {0}: unknown key(s) {1!s}. Have you misspelled them?".format(entry, list(extraneous_keys)))

	return sane_attributes

# reads the metadata file and returns a dict mapping each entry to the attributes
# specified. one can rely upon that they conform to the attribute_schema
def parse(filename):
	parser = configparser.RawConfigParser(dict_type = OrderedDict)
	try:
		parser.readfp(codecs.open(filename, encoding='UTF-8', errors='strict'))
		return OrderedDict((sec, validate(sec, dict(parser.items(sec)))) for sec in parser.sections())
	except UnicodeDecodeError as ex:
		error(u"In file {0}: invalid UTF-8 character".format(filename), exception = ex, abort = True)

# reads the version file, composed of pairs of version number and release date
def read_versions(filename):
	versions = []
	try:
		with open(filename) as input:
			for line in input:
				try:
					version, release_date = line.split(" = ")
				except ValueError as ex:
					error(u"In file {0}: Malformed association {1}".format(filename, line), exception = ex)
					error("Not processing releases")
					return []
				else:
					versions.append((version, release_date.strip()))
	except Exception as ex:
		error(u"In file {0}: error".format(filename), exception = ex)
		error("Not processing releases")
		return []
	else:
		versions.sort(key = itemgetter(1), reverse = True)
		return versions

# reads the list of entry releases (metadata/releases)
def associate_releases(entries, versions, filename):
	for _, attributes in entries.items():
		attributes['releases'] = OrderedDict()
	prog = re.compile(release_pattern)
	warnings = {}
	try:
		with open(filename) as input:
			lines = []
			for line in input:
				line = line.strip()
				result = prog.match(line)
				try:
					entry, date = result.groups()
				except ValueError as ex:
					error(u"In file {0}: Malformed release {1}".format(filename, line.replace), exception = ex)
				else:
					if not entry in entries:
						if not entry in warnings:
							warnings[entry] = [line]
						else:
							warnings[entry].append(line)
					else:
						lines.append((entry, date))
		for entry, releases in warnings.items():
			warn(u"In file {0}: In release(s) {1!s}: Unknown entry {2}".format(filename, releases, entry))
		lines.sort(reverse = True)
		for line in lines:
			found = False
			entry, date = line
			for version_number, version_date in versions:
				if version_date <= date:
					entry_releases = entries[entry]['releases']
					if version_number not in entry_releases:
						entry_releases[version_number] = []
					entry_releases[version_number].append(date)
					found = True
					break
			if not found:
				warn(u"In file {0}: In release {1}: Release date {2} has no matching version".format(filename, line, date))
	except Exception as ex:
		error(u"In file {0}: error".format(filename), exception = ex)
		error("Not processing releases")

def parse_status(filename):
	with open(filename) as input:
		data = json.load(input)

		build_data = data['build_data']
		status = dict()
		for entry in data['entries']:
			status[entry['entry']] = entry['status']

		return build_data, status

def add_status(entries, status):
	for e in entries:
		if e in status:
			entries[e]['status'] = status[e]
		else:
			entries[e]['status'] = "skipped"



if __name__ == "__main__":
	parser = OptionParser(usage = "Usage: %prog [--no-warn] [--debug] [--check] [--dest=DEST_DIR] [--status=STATUS_FILE] --metadata=METADATA_DIR THYS_DIR")
	parser.add_option("--no-warn", action = "store_false", dest = "enable_warnings", help = "disable output of warnings")
	parser.add_option("--check", action = "store_true", dest = "do_check", help = "compare the contents of the metadata file with actual file system contents")
	parser.add_option("--dest", action = "store", type = "string", dest = "dest_dir", help = "generate files for each template in the metadata directory")
	parser.add_option("--debug", action = "store_true", dest = "enable_debug", help = "display debug output")
	parser.add_option("--metadata", action = "store", type = "string", dest = "metadata_dir", help = "metadata location")
	parser.add_option("--status", action = "store", type = "string", dest = "status_file", help = "status file location (devel)")
	parser.add_option("--download", action = "store_true", dest = "build_download", help = "build download page")


	(_, args) = parser.parse_args(argv, values = options)
	if len(args) != 2:
		parser.error("You must supply the theories directory. For usage, supply --help.")

	thys_dir = args[1]
	metadata_dir = options.metadata_dir

	# parse metadata
	entries = parse(os.path.join(metadata_dir, "metadata"))
	versions = read_versions(os.path.join(metadata_dir, "release-dates"))
	associate_releases(entries, versions, os.path.join(metadata_dir, "releases"))
	if len(entries) == 0:
		warn("In metadata: No entries found")

	# generate depends-on, used-by entries, lines of code and number of lemmas
	# by using an afp_dict object
	afp_dict = afpstats.afp_dict(entries, thys_dir)
	afp_dict.build_stats()
	for e in entries:
		entries[e]['depends-on'] = list(map(str, afp_dict[e].imports))
		entries[e]['used-by'] = list(map(str, afp_dict[e].used))

	# perform check
	if options.do_check:
		count = check_fs(entries, thys_dir)
		output = "Checked directory {0}. Found {1} warnings.".format(thys_dir, count)
		color = 'yellow' if count > 0 else 'green'
		print(colored(output, color, attrs=['bold']))

	# perform generation
	if options.dest_dir:
		if options.is_devel():
			(build_data, status) = parse_status(options.status_file)
			for a in afp_dict:
				if a in status:
					afp_dict[a].status = status[a]
				else:
					afp_dict[a].status = "skipped"
		else:
			build_data = dict()

		is_devel = options.status_file is not None
		builder = templates.Builder("admin/sitegen-lib/templates", "web",
			entries, afp_dict, is_devel)
		builder.generate_topics()
		builder.generate_index()
		builder.generate_entries()
		builder.generate_statistics()
		for s in ["about", "citing", "updating", "search",
			"submitting", "using"]:
			builder.generate_standard(s + ".shtml", s + ".tpl")
		builder.generate_rss(30)
		if options.build_download:
			builder.generate_download()
		#TODO: look over it one more time
		if options.is_devel():
			builder.generate_status(build_data)

