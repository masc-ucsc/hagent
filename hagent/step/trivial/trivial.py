#!/usr/bin/env python3
# See LICENSE for details

from hagent.core.step import Step


# Trivial example of extending the Pass class
class Trivial(Step):
    def run(self, data):
        # Simply return the input data without modification
        return data


if __name__ == '__main__':  # pragma: no cover
    trivial_step = Trivial()
    trivial_step.main()
