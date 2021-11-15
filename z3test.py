#!/usr/bin/env python3

import unittest
import os
import shutil
import tempfile
import subprocess as sub

root_dir = (
    sub.check_output("git rev-parse --show-toplevel", shell=True).decode().strip()
)


class TestExamples(unittest.TestCase):
    def test_examples(self):
        path = os.path.join(root_dir, "test")
        pgm_path = os.path.join(path, "pgms")
        for example in os.listdir(pgm_path):
            script_path = os.path.join(pgm_path, example)
            output_path = os.path.join(path, "pgm_outputs", "{}.out".format(example))
            print("Testing {}".format(script_path))
            with tempfile.NamedTemporaryFile() as tmpfile:
                tee_path = tmpfile.name
                sub.run(
                    "python3 {} | tee {}".format(script_path, tee_path),
                    shell=True,
                    check=True,
                )
                try:
                    sub.run(
                        "diff {} {}".format(output_path, tee_path),
                        shell=True,
                        check=True,
                    )
                except sub.CalledProcessError as e:
                    print("Output mismatch")
                    print("Expected output in: {}".format(output_path))
                    f = open(tee_path, "r")
                    print("Actual ouput: {}".format(f.read()))
                    f.close()
                    raise e


if __name__ == "__main__":
    unittest.main()
