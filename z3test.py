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
            process_result = sub.run(
                ["python3", script_path],
                stdout=sub.PIPE,
                stderr=sub.STDOUT,  # merge output streams
            )
            with open(output_path, "r") as f:
                expected_output = f.read()

            if expected_output != process_result.stdout.decode():
                print("Output mismatch")
                print("Expected output: <{}>".format(process_result.stdout.decode()))
                print("Actual ouput: <{}>".format(expected_output))
                assert False, "Output mismatch"


if __name__ == "__main__":
    unittest.main()
