#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Keeps track of symbols used throughout other files. Allows serialization and addition of
metadata to each symbol.

@author: Keith Allatt
@version: 1.1
"""

from typing import Union
import json
import abc
import os.path


class Symbolic:
    """ Global class type for serialization. """
    def __init__(self, str_repr, item):
        self.str_repr = str_repr
        self.item = item


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

    def __eq__(self, other):
        if type(other) != SymbolSet:
            return False
        other: SymbolSet
        return self._symbol_set == other._symbol_set

    def __getitem__(self, item):
        class UnicodeSymbol(Symbolic, metaclass=abc.ABCMeta):
            def __init__(self, str_repr, item_):
                super().__init__(str_repr, item_)

            def __str__(self):
                return self.str_repr

            def __eq__(self, other):
                return str(self) == str(other)

        symbol = UnicodeSymbol(self._symbol_set[item]['unicode'], item)

        if 'doc' in self._symbol_set[item].keys():
            symbol.__doc__ = self._symbol_set[item]['doc']
        else:
            symbol.__doc__ = f"""Symbol [ {item} ] -> [ {str(symbol)} ]"""

        return symbol

    def __str__(self):
        return json.dumps(self._symbol_set, indent=4)


class LogicalSymbolSet(SymbolSet):
    """ Logical Connective symbols. """
    def __init__(self, *args):
        super().__init__('SymbolSets/logical_symbols.json')


class MathSymbolSet(SymbolSet):
    """ General Mathematical symbols. """
    def __init__(self, *args):
        super().__init__('SymbolSets/math_symbols.json')


class PredicateSymbolSet(SymbolSet):
    """ Predicate Logical symbols. """
    def __init__(self, *args):
        super().__init__('SymbolSets/predicate_symbols.json')


class TruthSymbolSet(SymbolSet):
    """ Truth value symbols. """
    def __init__(self, *args):
        super().__init__('SymbolSets/truth_symbols.json')
