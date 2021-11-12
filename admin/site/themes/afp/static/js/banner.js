document.addEventListener("DOMContentLoaded", () => {
    if (localStorageTest() === true) {
        const banner = document.getElementById("banner");
        if (banner) {
            const bannerID = banner.getAttribute("data-id");
            if (localStorage.getItem("banner-" + bannerID) === "true") {
                banner.style = "display: none";
            }

            const close = document.getElementById("close");
            if (close) {
                // show the close button if we have JS and local storage access
                close.style = "";

                close.addEventListener("click", () => {
                    banner.style = "display: none";
                    localStorage.setItem("banner-" + bannerID, "true");
                });
            }
        }
    }
});

function localStorageTest() {
    if (typeof localStorage !== "undefined") {
        localStorage.setItem("test", "yes");
        if (localStorage.getItem("test") === "yes") {
            localStorage.removeItem("test");
            return true;
        }
    }
    return false;
}
