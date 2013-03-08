#! /usr/bin/python

from sys import argv, stderr

def error(message, exception = None, abort = False):
	print >> stderr, ("Error: {0}".format(message))
	if exception:
		error("*** exception message:")
		error("*** {0!s} {1!s}".format(exception, type(exception)))
	if abort:
		error("Fatal. Aborting")
		exit(1)

def read_report(filename):
	entries = []
	with open(filename) as f:
		for line in f:
			try:
				entry, status = line.split(": ")
			except ValueError as ex:
				error("In file {0}: Malformed line {1}".format(filename, line), 
					  exception = ex, abort = True)
			else:
				entries.append((entry, status.strip()))
	return dict(entries)

def read_status_template(filename):
	n = 0
	lines = [[]]
	with open(filename) as f:
		for line in f:
			if line=="----\n":
				n = n+1
				lines.append([])
			else:
				lines[n].append(line)			
	if len(lines) != 3:
		error("Wrong number of sections in template {0}.".format(filename), 
			  abort = True)
	return (lines[0], lines[1], lines[2])

def status_line(entry,status):
	return ('    <tr><td class="status-{1}">[{1}]</td><td class="entry">'
            '<a href=\"devel-entries/{0}.shtml\">{0}</a></td></tr>').format(entry,status)

def write_entries(entries, template, isa_ver, isa_date, afp_ver, afp_date):
	(header,div,footer) = template
	
	for line in header:
		print line,
	
	print '   <table style="margin-left: 30pt;"><tbody>'
	print '   <tr><td>Isabelle revision:</td><td>' \
	          '<a href="http://isabelle.in.tum.de/repos/isabelle/changelog/{0}">' \
	          '{0}</a> - {1}</td></tr>'.format(isa_ver, isa_date)
	print '   <tr><td>AFP revision:</td><td>'\
	          '<a href="http://sourceforge.net/p/afp/code/ci/{0}">' \
	          '{0}</a> - {1}</td></tr>'.format(afp_ver, afp_date)
	print '   </tbody></table>'
	
	for line in div:
		print line,
	
	for entry in sorted(entries.keys()):
		print status_line(entry,entries[entry])
	
	for line in footer:
		print line,
	
if __name__ == "__main__":
	if len(argv) != 7:
		print "Usage: "+argv[0]+ \
			  " report-name template-name isa-ver isa-date afp-ver afp-date"
		exit(1)
	report_name, template_name = argv[1], argv[2]
	isa_version, isa_date = argv[3], argv[4]
	afp_version, afp_date = argv[5], argv[6]
	entries = read_report(report_name)
	template = read_status_template(template_name)
	write_entries(entries, template, isa_version, isa_date, afp_version, afp_date)
