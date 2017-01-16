# pattern for release tarball filename
release_pattern = """^afp-(.*)-([0-9\-]{10}).tar.gz$"""

### licenses

# key : (title, url)
#   'key' denotes the short name of the license (e. g. 'LGPL')
#   'title' denotes the display title of the license (e. g. 'GNU Lesser General Public License (LGPL)')
#   'url' contains the url of the license text

licenses = {
	'LGPL': ("GNU Lesser General Public License (LGPL)", "http://isa-afp.org/LICENSE.LGPL"),
	'BSD': ("BSD License", "http://isa-afp.org/LICENSE"),
}



### options

class Options(object):
	def __init__(self):
		self.enable_debug = False
		self.enable_warnings = True
		self.dest_dir = None
		self.do_check = False
		self.metadata_dir = None
		self.status_file = None
		self.build_download = False
	def is_devel(self):
		return self.status_file is not None

options = Options()
