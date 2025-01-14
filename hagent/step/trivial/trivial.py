#!/usr/bin/env python3
# See LICENSE for details

from hagent.core.step import Step
from typing import Dict


# Trivial example of extending the Pass class
class Trivial(Step):
    def setup(self):
        super().setup()  # superclass

    def run(self, data: Dict):
        ret = data.copy()
        ret['added_field_trivial'] = 'sample'
        # Simply return the input data without modification
        return ret


if __name__ == '__main__':  # pragma: no cover
    trivial_step = Trivial()
    trivial_step.parse_arguments()
    trivial_step.setup()
    trivial_step.step()
