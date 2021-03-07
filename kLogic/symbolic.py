from typing import Union
import json
import os.path

class SymbolSet:
    """ Symbol set that comes with more information per symbol. """
    def __init__(self, file_out: str = None):
        self.file_path = file_out
        self._symbol_set = {}

        if self.file_path is not None:
            self.read_file()

    def save_to_file(self):
        if self.file_path is None:
            return False
        with open(self.file_path, 'w') as file:
            file.write(json.dumps(self._symbol_set, indent=4))

    def read_file(self):
        if self.file_path is None:
            return False
        if os.path.exists(self.file_path):
            with open(self.file_path, 'r') as file:
                self._symbol_set = json.loads(file.read())
                for key in self._symbol_set:
                    unicode = self._symbol_set[key]['unicode']
                    if type(unicode) is int:
                        self._symbol_set[key]['unicode'] = chr(unicode)
        else:
            prepend = os.sep.join(str(__file__).split(os.sep)[:-1])
            if not self.file_path.startswith(prepend):
                self.file_path = prepend + os.sep + self.file_path
                self.read_file()
            return False

    def put(self, symbol_name: str, symbol_char: Union[str, int], on_collision='reject'):
        if on_collision == 'reject':
            self._symbol_set[symbol_name] = {
                'unicode': symbol_char
            }

        pass

    def get(self, symbol_name: str, default=None):
        if symbol_name not in self._symbol_set.keys():
            return default

        return self._symbol_set[symbol_name]

    def items(self):
        return {key: self._symbol_set[key]['unicode'] for key in self._symbol_set.keys()}.items()

    def keys(self):
        return self._symbol_set.keys()

    def __getitem__(self, item):
        return self._symbol_set[item]['unicode']

    def __str__(self):
        return json.dumps(self._symbol_set, indent=4)


class LogicalSymbolSet(SymbolSet):
    """ Logical Connective symbols. """
    def __init__(self, *args):
        super().__init__('SymbolSets/logical_symbols.json')


class MathSymbolSet(SymbolSet):
    """ Logical Connective symbols. """
    def __init__(self, *args):
        super().__init__('SymbolSets/math_symbols.json')


class PredicateSymbolSet(SymbolSet):
    """ Logical Connective symbols. """
    def __init__(self, *args):
        super().__init__('SymbolSets/predicate_symbols.json')


class TruthSymbolSet(SymbolSet):
    """ Logical Connective symbols. """
    def __init__(self, *args):
        super().__init__('SymbolSets/truth_symbols.json')
