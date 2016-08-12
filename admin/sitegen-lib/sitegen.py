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

	# generate depends-on, used-by entries, lines of code and number of lemmas
	# by using an afp_dict object
	afp_dict = afpstats.afp_dict(entries, thys_dir)
	afp_dict.build_stats()
	for e in entries:
		entries[e]['depends-on'] = list(map(str, afp_dict[e].imports))
		entries[e]['used-by'] = list(map(str, afp_dict[e].used))
	loc = 0
	num_lemmas = 0
	for _k, a in afp_dict.items():
		loc += a.loc
		num_lemmas += a.lemmas
	STAT_FIGURES['loc'] = loc
	STAT_FIGURES['num_lemmas'] = num_lemmas
	STAT_FIGURES['num_authors'] = len(afp_dict.authors)

	# Generate data for graphs in statistics page
	articles_years = dict()
	loc_years = dict()
	for _k, a in afp_dict.items():
		try:
			articles_years[a.publish_date.year] += 1
		except KeyError:
			articles_years[a.publish_date.year] = 1
		try:
			loc_years[a.publish_date.year] += a.loc
		except KeyError:
			loc_years[a.publish_date.year] = a.loc
	author_years = dict()
	for _k, a in afp_dict.authors.items():
		first_year = min([e.publish_date.year for e in a.articles])
		try:
			author_years[first_year] += 1
		except KeyError:
			author_years[first_year] = 1
	author_years_series = author_years.copy()
	for y in sorted(articles_years)[1:]:
		articles_years[y] += articles_years[y - 1]
		loc_years[y] += loc_years[y - 1]
		author_years_series[y] += author_years_series[y - 1]
	most_used = sorted([(a.name, len(a.used)) for _k, a in afp_dict.items()],
	                     key = lambda x: (-x[1], x[0]))
	most_used10 = most_used[:10]
	i = 10
	while most_used10[-1][1] == most_used[i][1]:
		most_used10.append(most_used[i])
		i += 1
	STAT_FIGURES['articles_years'] = articles_years
	STAT_FIGURES['loc_years'] = loc_years
	STAT_FIGURES['author_years'] = author_years
	STAT_FIGURES['author_years_series'] = author_years_series
	STAT_FIGURES['most_used10'] = most_used10
	all_articles = sorted(afp_dict, key = lambda x: afp_dict[x].publish_date)
	years = [2004]
	# FIXME: All of it
	for i in range(1, len(all_articles)):
		if (afp_dict[all_articles[i]].publish_date.year !=
		  afp_dict[all_articles[i - 1]].publish_date.year):
			years.append(afp_dict[all_articles[i]].publish_date.year)
		else:
			years.append("")
	years += ""
	STAT_FIGURES['all_articles'] = all_articles
	STAT_FIGURES['years_loc_articles'] = years
	STAT_FIGURES['loc_articles'] = [afp_dict[a].loc for a in all_articles]

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
