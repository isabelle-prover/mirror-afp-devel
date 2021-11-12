function loadSearch(input, keywords) {
    var suggestIndex = new FlexSearch({
        encode: "icase",
        tokenize: "forward",
        doc: {
            id: "id",
            field: "keyword",
        },
    });

    var indices = {
        suggest: suggestIndex,
    };

    indices["suggest"].add(keywords);

    input.addEventListener("keyup", function (event) {
        switch (event.key) {
            case "Enter":
            case "Up":
            case "ArrowUp":
            case "Down":
            case "ArrowDown":
            case "Left":
            case "ArrowLeft":
            case "Right":
            case "ArrowRight":
            case "Escape":
                break;
            default:
                if (this.value && this.value.length > 1) {
                    executeSearch(indices, this.value);
                }
        }
    });


    input.addEventListener("keydown", function (event) {
        switch (event.key) {
            case "Enter":
                event.preventDefault(); // prevent the form from being submitted
                handleSubmit(this.value);
                break;
            default:
        }
    });

    input.addEventListener("change", function () {
        handleSubmit(this.value);
    });
}

function executeSearch(indices, searchQuery) {
    var suggestResults = indices["suggest"].search({
        query: searchQuery,
        limit: 10,
    });
    
    if (!(suggestResults.length === 1 && suggestResults[0].keyword === searchQuery)) {
        filterAutocomplete(suggestResults);
    } else {
        filterAutocomplete();
    }
}

function handleSubmit(value) {
    if (typeof history.pushState !== "undefined") {
        document.location = window.location.origin + "/search/?s=" + value;
    } else {
        var url = "TODO";
        window.location.assign(url);
    }
}

// Autocomplete ------------------------------------------------------------------------

function filterAutocomplete(values) {
    const list = document.getElementById("autocomplete");
    if (list) {
        if (values) {
            let i = 0;
            for (let value of values) {
                let elem = document.createElement("option");
                elem.value = value.keyword;
                if (i < list.childNodes.length) {
                    list.childNodes[i].replaceWith(elem);
                    i++;
                } else {
                    list.appendChild(elem);
                }
            }
            if (values.length < list.childNodes.length) {
                for (let j = 0; j < list.childNodes.length - values.length; j++) {
                    list.removeChild(list.lastChild);
                }
            }
        } else {
            while (list.firstChild) {
                list.removeChild(list.lastChild);
            }
        }
    }
}

document.addEventListener("DOMContentLoaded", function () {
    var input = document.getElementById("searchInput");
    var button = document.getElementById("searchButton");
    if (button) {
        button.addEventListener("click", () => {
            handleSubmit(input.value);
        });
    }

    Promise.all([fetch("/data/keywords.json")])
        .then(function (responses) {
            // Get a JSON object from each of the responses
            return Promise.all(responses.map((response) => response.json()));
        })
        .then((data) => loadSearch(input, ...data));
});
