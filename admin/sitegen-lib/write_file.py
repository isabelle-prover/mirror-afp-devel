import json
import os


def write_file(file, data, write=True, overwrite=False):
    file_exists = os.path.isfile(file)

    if file_exists and not overwrite:
        with open(file) as r:
            original_data = json.load(r)

        data = {**original_data, **data}

    # Only write file if write or if file doesn't exist
    # Or, only don't write if write is false and file exists
    if not file_exists or write:
        with open(file, "w", encoding="utf-8") as w:
            json.dump(data, w, ensure_ascii=False, indent=4)
