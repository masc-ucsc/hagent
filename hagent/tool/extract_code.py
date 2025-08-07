import re
from abc import abstractmethod

from hagent.core.tracer import TracerABCMetaClass


class Extract_code(metaclass=TracerABCMetaClass):
    @abstractmethod
    def parse(self, prompt: str, verilog_path: str) -> list[str]:
        pass

    def extract_codeblock(self, text: str) -> str:
        if text is None:
            return ''

        pattern = re.compile(r'```(?:\w+)?\n?([\s\S]*?)```', re.MULTILINE)
        matches = pattern.findall(text)

        if matches:
            code = '\n\n'.join(match.strip() for match in matches)
        else:
            code = text.replace('```', '').strip()

        code = code.replace('`', '')

        return code


class Extract_code_verilog(Extract_code):
    def parse(self, prompt: str, verilog_path: str = '') -> list[str]:
        txt = self.extract_codeblock(prompt)
        txt = txt.replace('\\', '')

        modules = []
        current_module = ''
        preprocessor_lines = []
        in_module = False
        
        for line in txt.splitlines():
            if in_module:
                current_module += line + '\n'
                if 'endmodule' in line:
                    in_module = False
                    # Add any preprocessor directives at the beginning of the module
                    full_module = '\n'.join(preprocessor_lines) + ('\n' if preprocessor_lines else '') + current_module
                    modules.append(full_module)
                    current_module = ''
                    preprocessor_lines = []  # Reset for next module
            else:
                s = line.strip()
                if (
                    s.startswith('`include')
                    or s.startswith('`define')
                    or s.startswith('`if')
                    or s.startswith('`else')
                    or s.startswith('`endif')
                ):
                    preprocessor_lines.append(s)
                elif 'module ' in line:
                    in_module = True
                    current_module += s + '\n'

        # If we have standalone preprocessor directives without any modules, include them
        if preprocessor_lines and not modules:
            modules.append('\n'.join(preprocessor_lines))

        return modules


class Extract_code_chisel(Extract_code):
    def parse(self, prompt: str, verilog_path: str = '') -> list[str]:
        txt = self.extract_codeblock(prompt)
        txt = txt.replace('\\', '')

        answer = ''
        capture = False
        for line in txt.splitlines():
            if 'import chisel' in line:
                capture = True
            if capture:
                answer += line + '\n'

        if answer == '':
            answer = txt
        return [answer] if answer else []


class Extract_code_pyrtl(Extract_code):
    def parse(self, prompt: str, verilog_path: str) -> list[str]:
        txt = self.extract_codeblock(prompt)
        txt = txt.replace('\\', '')

        answer = ''
        capture = False
        for line in txt.splitlines():
            if 'import pyrtl' in line:
                capture = True
            if capture:
                answer += line + '\n'

        if answer == '':
            answer = txt

        pattern = r"(with open\()(.*?)(, 'w')"
        if re.search(pattern, answer):
            replacement = r'\1' + "'" + str(verilog_path) + "'" + r'\3'
            answer = re.sub(pattern, replacement, answer)
        return [answer] if answer else []


class Extract_code_dslx(Extract_code):
    def parse(self, prompt: str, verilog_path: str = '') -> list[str]:
        txt = self.extract_codeblock(prompt)
        txt = txt.replace('\\', '')

        answer = ''
        capture = False
        for line in txt.splitlines():
            if ('struct' in line) or ('fn ' in line):
                capture = True
            if capture:
                if '```' in line:
                    return [answer] if answer else []
                answer += line + '\n'

        if answer == '':
            answer = txt
        return [answer] if answer else []


class Extract_code_default(Extract_code):
    def parse(self, prompt: str, verilog_path: str = '') -> list[str]:
        txt = self.extract_codeblock(prompt)
        txt = txt.replace('\\', '')

        return [txt] if txt else []


def get_extract_code(lang: str) -> Extract_code:
    txt = lang.lower()
    if txt == 'verilog':
        return Extract_code_verilog()
    elif txt == 'chisel':
        return Extract_code_chisel()
    elif txt == 'pyrtl':
        return Extract_code_pyrtl()
    elif txt == 'dslx':
        return Extract_code_dslx()
    elif txt == 'default':
        return Extract_code_default()
    else:
        raise ValueError('Unsupported Language type in Extract_code')


# extractor = get_hdlang("VerIloG")
