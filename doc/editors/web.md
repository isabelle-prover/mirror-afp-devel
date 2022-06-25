Web site & Site generator
-------------------------

The site generation can be run directly with `isabelle afp_site_gen`.
Note that you need to have installed the AFP as an Isabelle component
(`isabelle components -u <DIR>`) and resolved all component dependencies
(`isabelle components -a`).
To run the site generation without any arguments, you can invoke the script:

    ./admin/sitegen

The output will be written to the `web` folder, which is supposed to be
committed into the repository. It can be inspected by opening any of the
contained HTML files in the browser.

Changing static content, e.g. the submission guidelines, works by editing the
appropriate markdown file in `admin/site/content` and re-running the `sitegen` script.
The `afp_site_gen` tool also has a development mode which makes changes in content
immediately visible.

To publish website changes without publishing a new entry, you can use the
`publish` script with the `-` argument:

    ./admin/publish -
