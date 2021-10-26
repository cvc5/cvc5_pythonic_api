#!/usr/bin/env python

import unittest
import os
import shutil
import tempfile
import subprocess as sub

tempfile.NamedTemporaryFile
root_dir = (
    sub.check_output("git rev-parse --show-toplevel", shell=True).decode().strip()
)


class TestExamples(unittest.TestCase):
    def test_examples(self):
        path = os.path.join(root_dir, "test")
        pgm_path = os.path.join(path, "pgms")
        for example in os.listdir(pgm_path):
            script_path = os.path.join(pgm_path, example)
            output_path = os.path.join(path, "pgm_outputs", f"{example}.out")
            print(f"Testing {script_path}")
            with tempfile.NamedTemporaryFile() as tmpfile:
                tee_path = tmpfile.name
                sub.run(
                    f"python {script_path} | tee {tee_path}", shell=True, check=True
                )
                try:
                    sub.run(f"diff {output_path} {tee_path}", shell=True, check=True)
                except sub.CalledProcessError as e:
                    print("Output mismatch")
                    print(f"Expected: {output_path}")
                    print(f"Actual: {tee_path}")
                    raise e


if __name__ == '__main__':
    unittest.main()
