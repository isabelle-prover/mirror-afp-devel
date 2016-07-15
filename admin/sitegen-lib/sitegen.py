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
from templates import *



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
					app = appkey[:len(shortkey)]
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


# look for templates in the metadata directory according to the definitions
# in the global configuration
def scan_templates(entries, build_data):
	for template in templates.keys():
		try:
			template_filename = os.path.join(metadata_dir, template + template_suffix)
			if os.path.exists(template_filename):
				handle_template(entries, build_data, template, read_template(template_filename))
			else:
				raise(Exception("File not found. Make sure the files defined in 'templates' dict exist".format(template_filename)))
		except UnicodeDecodeError as ex:
			error(u"In file {0}: invalid UTF-8 character".format(template_filename), exception = ex)
			stats.failed_tpls += 1
			return
		except Exception as ex:
			error(u"In template {0}: File couldn't be processed".format(template_filename), exception = ex)
			stats.failed_tpls += 1
			return

# reads a template line by line and returns a list
# Suppose you have the following template content:
#   foo
#   bar
#   <!--gen-->
#   baz
#   <!--gen:param-->
#   qux
# then you will get the following result:
# [
#   (['foo', 'bar'], ''),
#   (['baz'], 'param'),
#   (['qux'], None)
# ]
def read_template(template_filename):
	lines = []
	result = []
	with codecs.open(template_filename, encoding='UTF-8', errors='strict') as input:
		debug(u"Reading template {0}".format(template_filename))
		found = False
		for line in input:
			stripped = line.strip()
			if stripped.startswith(magic_str_start) and stripped.endswith(magic_str_end):
				found = True

				param = stripped[len(magic_str_start):len(stripped)-len(magic_str_end)]
				if param.startswith(":"):
					param = param[1:].strip()
					debug(u"In file {0}: Found generator with parameter {1}".format(template_filename, param))
				else:
					debug(u"In file {0}: Found generator without parameter".format(template_filename))

				result.append((lines, param))
				lines = []
			else:
				lines.append(line)
		if not found:
			warn(u"In file {0}: No generator found".format(template_filename))

	result.append((lines, None))
	return result

# opens a file, invokes the generator and writes the result
def write_output(filename, content, generator):
	stats.gens += 1
	debug(u"Writing result to {0}".format(filename))
	failed = False
	try:
		with codecs.open(filename, mode='w', encoding='UTF-8', errors='strict') as output:
			for lines, param in content:
				for line in lines:
					output.write(line)
				if param != None:
					try:
						if param == '':
							result = generator()
						else:
							result = generator(param = param)
					except Exception as ex:
						failed = True

						error(u"For output file {0}: generator failed".format(filename), exception = ex)
					else:
						output.write(result)
	except Exception as ex:
		failed = True
		error(u"For output file {0}: error".format(filename), exception = ex)
	finally:
		if failed:
			stats.failed_gens += 1

# main function for handling a template
# Steps:
# * search the appropriate generator function
# * create destination directories
# * call write_output for each entry or for all entries together
def handle_template(entries, build_data, template, content):
	dir, generator, for_each_func, devel = templates[template]

	if devel and not options.is_devel(): return

	extra_args = dict()
        if devel: extra_args['build_data'] = build_data

	stats.tpls += 1

	dest_subdir = os.path.join(options.dest_dir, dir)
	try:
		os.makedirs(dest_subdir)
	except Exception as ex:
		if not os.path.exists(dest_subdir):
			error(u"In template {0}: directory {1} couldn't be created".format(template, dest_subdir), exception = ex)
			return

	if for_each_func:
		for entry, attributes in entries.items():
			output_filename = os.path.join(dest_subdir, for_each_func(entry) + output_suffix)
			write_output(output_filename, content, partial(generator, entry, attributes, **extra_args))
	else:
		output_filename = os.path.join(dest_subdir, template + output_suffix)
		write_output(output_filename, content, partial(generator, entries.items(), **extra_args))

def normpath(path, *paths):
	"""Return a normalized and absolute path (depending on current working directory)"""
	return os.path.abspath(os.path.join(path, *paths))

def theory_dict(entries):
	"""Creates a dict with .thy files as key and the corresponding theory as value"""
	thys = dict()
	for entry in entries:
		for thy in entries[entry]['thys']:
			thys[thy] = entry
	return thys

def add_theories(entries, thy_dir):
	"""Add a set of paths to .thy files of an entry to entries[e]['thys']"""
	for entry in entries:
		entries[entry]['thys'] = set()
		for root, _dirnames, filenames in os.walk(os.path.join(thy_dir, entry)):
			for f in filenames:
				if f.endswith(".thy"):
					entries[entry]['thys'].add(normpath(root, f))

def add_theory_dependencies(entries):
	"""Adds dependencies by checking .thy-files"""
	thys = theory_dict(entries)
	pattern0 = re.compile("imports(.*?)begin", re.DOTALL)
	for t in thys:
		with open(t, 'r') as f:
			content = f.read()
		match0 = pattern0.search(content)
		if match0 is not None:
			# Go through imports and check if its a file in the AFP
			# if yes, add dependency
			imps = [normpath(os.path.dirname(t), x.strip(' \t"') + ".thy")
				for x in match0.group(1).split()]
			for i in imps:
				if i in thys:
					entries[thys[t]]['depends-on'].add(thys[i])

def add_root_dependencies(entries, thy_dir):
	"""Adds dependencies by checking ROOT files"""
	thys = theory_dict(entries)
	for entry in entries:
		root = normpath(thy_dir, entry, "ROOT")
		with open(root, 'r') as root_file:
			root_content = root_file.read()
		#check for imports of the form "session ... = ... (AFP) +"
		for line in root_content.splitlines():
			if line.startswith("session"):
				for word in [x.strip(' \t"') for x in line.split()]:
					if word in entries:
						entries[entry]['depends-on'].add(word)
		#run through every word in the root file and check if there's a corresponding AFP file
		for word in [x.strip(' \t"') for x in root_content.split()]:
			#catch Unicode error, since paths can only contain ASCII chars
			try:
				theory = normpath(thy_dir, entry, word + ".thy")
				if theory in thys:
					entries[entry]['depends-on'].add(thys[theory])
			except UnicodeDecodeError:
					pass

def remove_self_imps(entries):
	"""Remove self imports in "depends-on"-field"""
	for entry in entries:
		try:
			entries[entry]['depends-on'].remove(entry)
		except KeyError:
			pass

def add_used_by(entries):
	for entry in entries:
		entries[entry]['used_by'] = set()
	for entry in entries:
		for d in entries[entry]['depends-on']:
			entries[d]['used_by'].add(entry)

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

	# generate depends-on and used-by entries
	for e in entries: entries[e]['depends-on'] = set()
	add_theories(entries, thys_dir)
	add_theory_dependencies(entries)
	add_root_dependencies(entries, thys_dir)
	remove_self_imps(entries)
	add_used_by(entries)

	# perform check
	if options.do_check:
		count = check_fs(entries, thys_dir)
		output = "Checked directory {0}. Found {1} warnings.".format(thys_dir, count)
		color = 'yellow' if count > 0 else 'green'
		print(colored(output, color, attrs=['bold']))

	# perform generation
	if options.dest_dir:
		# parse status file
		if options.is_devel():
			(build_data, status) = parse_status(options.status_file)
			add_status(entries, status)
                else:
			build_data = dict()

		# parse template format
		magic_str_pos = magic_str.index("$")
		magic_str_start = magic_str[:magic_str_pos]
		magic_str_end = magic_str[magic_str_pos+1:]

		stats = Stats()
		scan_templates(entries, build_data)
		print(stats)
