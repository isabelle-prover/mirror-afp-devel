document.addEventListener("DOMContentLoaded", function () {
    const content = document.getElementById("copyText").innerHTML;
    const filename = document.getElementById("bibtexFileName").innerHTML;
    document.getElementById("copyBibtex").addEventListener("click", () => {
        navigator.clipboard.writeText(content);
    });

    const a = document.getElementById("downloadBibtex");
    var blob = new Blob([content], { type: "text/plain" });
    var url = URL.createObjectURL(blob);
    a.setAttribute("href", url);
    a.setAttribute("download", filename + ".bib");
});
