/* constants */

const ID_COPY_TEXT = 'copy-text'
const ID_COPY_BIBTEX = 'copy-bibtex'
const ID_BIBTEX_FILE = 'bibtex-filename'
const ID_DOWNLOAD_BIBTEX = 'download-bibtex'


/* setup */

const init_entry = () => {
  const content = document.getElementById(ID_COPY_TEXT).innerHTML
  const filename = document.getElementById(ID_BIBTEX_FILE).innerHTML
  document.getElementById(ID_COPY_BIBTEX).addEventListener('click', () => {
    navigator.clipboard.writeText(content)
  })

  const download_bibtex = document.getElementById(ID_DOWNLOAD_BIBTEX)
  const blob = new Blob([content], {type: "text/plain"})
  const url = URL.createObjectURL(blob)
  download_bibtex.setAttribute('href', url)
  download_bibtex.setAttribute('download', filename + '.bib')
}

document.addEventListener('DOMContentLoaded', init_entry)