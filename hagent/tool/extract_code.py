import re
from abc import ABC, abstractmethod


class Extract_code(ABC):
    @abstractmethod
    def parse(self, prompt: str, verilog_path: str) -> str:
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
    def parse(self, prompt: str, verilog_path: str="") -> str:
        txt = self.extract_codeblock(prompt)
        txt = txt.replace('\\', '')

        answer = ''
        in_module = False
        for line in txt.splitlines():
            if in_module:
                answer += line + '\n'
            else:
                s = line.strip()
                if (
                    s.startswith('`include')
                    or s.startswith('`define')
                    or s.startswith('`if')
                    or s.startswith('`else')
                    or s.startswith('`endif')
                ):
                    answer += s + '\n'
                elif 'module ' in line:
                    in_module = True
                    answer += s + '\n'

            if 'endmodule' in line:
                in_module = False

        return answer


class Extract_code_chisel(Extract_code):
    def parse(self, prompt: str, verilog_path: str) -> str:
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
        return answer


class Extract_code_pyrtl(Extract_code):
    def parse(self, prompt: str, verilog_path: str) -> str:
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
            return re.sub(pattern, replacement, answer)
        return answer


class Extract_code_dslx(Extract_code):
    def parse(self, prompt: str, verilog_path: str) -> str:
        txt = self.extract_codeblock(prompt)
        txt = txt.replace('\\', '')

        answer = ''
        capture = False
        for line in txt.splitlines():
            if ('struct' in line) or ('fn ' in line):
                capture = True
            if capture:
                if '```' in line:
                    return answer
                answer += line + '\n'

        if answer == '':
            answer = txt
        return answer

class Extract_code_default(Extract_code):
    def parse(self, prompt: str, verilog_path: str="") -> str:
        txt = self.extract_codeblock(prompt)
        txt = txt.replace('\\', '')

        return txt


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
