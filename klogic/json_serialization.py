#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""

@author: Keith Allatt
@version: 1.1
"""

import json
import re
import traceback
import klogic.symbolic as symbolic
import klogic.Propositional.logical as logical


def _stringify_type(object__):
    if type(object__) == type:
        return re.match(r"<class '(.+?)'>", str(object__)).groups()[0]
    return re.match(r"<class '(.+?)'>", str(object__.__class__)).groups()[0]

class JSONSerializer:
    """ Serialize arbitrary objects into json.  """
    def serialize(self, object_, ret_json=True):
        serialized = {
            "type": _stringify_type(object_)
        }

        if issubclass(type(object_), symbolic.Symbolic):
            object_: symbolic.Symbolic
            serialized.update({
                "type": _stringify_type(symbolic.Symbolic),
                "attributes": {
                    "str_repr": self.serialize(object_.str_repr, ret_json=False),
                    "item": self.serialize(object_.item, ret_json=False),
                }
            })
        elif type(object_) == logical.Atom:
            object_: logical.Atom
            serialized.update({"attributes": {
                "truth_value": self.serialize(object_.truth_value, ret_json=False),
                "name": self.serialize(object_.name, ret_json=False),
                "truth_table_cached": self.serialize(object_.truth_table_cached, ret_json=False),
                "truth_hash_cached": self.serialize(object_.truth_hash_cached, ret_json=False),
            }})
        elif issubclass(type(object_), logical.LogicalConnective):
            object_: logical.LogicalConnective

            serialized.update({
                "type": _stringify_type(logical.LogicalConnective),
                "attributes": {
                    "name": self.serialize(object_.name, ret_json=False),
                    "components": self.serialize(object_.components, ret_json=False),
                    "truth_table_cached": self.serialize(object_.truth_table_cached, ret_json=False),
                    "truth_hash_cached": self.serialize(object_.truth_hash_cached, ret_json=False),
                }
            })
        # PRIMITIVE TYPES
        elif serialized["type"] == "list":
            object_: list
            serialized.update({
                "attributes": [
                    self.serialize(element, ret_json=False) for element in object_
                ]
            })
        elif serialized["type"] == "dict":
            object_: dict
            serialized.update({
                "attributes": [
                    {
                        "key": self.serialize(key, ret_json=False),
                        "value": self.serialize(value, ret_json=False)
                    } for key, value in object_.items()
                ]
            })
        elif serialized["type"] == "tuple":
            object_: tuple
            serialized.update({
                "attributes": [
                    self.serialize(element, ret_json=False) for element in object_
                ]
            })
        else:
            if serialized["type"] not in ["int", "float", "bool", "str", "complex", "NoneType"]:
                raise NotImplementedError(f"Not Implemented {serialized['type']} [SERIALIZE]")

            serialized.update({
                "attributes": object_
            })

        return json.dumps(serialized, indent=1) if ret_json else serialized


class JSONDeserializer:
    def deserialize(self, json_repr=None, deserialized=None):
        try:
            if deserialized is None:
                deserialized = json.loads(json_repr)

            object_type = deserialized["type"]
            try:
                attr = deserialized['attributes']
            except KeyError:
                try:
                    attr = deserialized['attributes']
                except KeyError:
                    attr = {}
            if object_type == "list":
                return [self.deserialize(deserialized=at) for at in attr]
            elif object_type == "dict":
                print("dict")
                exit(0)
            elif object_type == "tuple":
                return tuple([self.deserialize(deserialized=at) for at in attr])
            elif object_type in ["int", "float", "bool", "str", "complex", "NoneType"]:
                return deserialized['attributes']
            if object_type == _stringify_type(logical.Atom):

                object_ = logical.Atom(
                    self.deserialize(deserialized=attr['name']),
                    self.deserialize(deserialized=attr['truth_value'])
                )

                object_.truth_table_cached = attr['truth_table_cached']
                object_.truth_hash_cached = attr['truth_hash_cached']
                return object_
            elif object_type == _stringify_type(logical.LogicalConnective):
                connective_type = attr['name']['attributes']['item']['attributes']

                components = self.deserialize(deserialized=attr['components'])

                return logical.LOGICAL_CONNECTIVES[connective_type](*components)
            else:
                raise NotImplementedError(f"Not Implemented {object_type} [DESERIALIZE]")
        except TypeError as e:
            print("ERROR", traceback.format_exception_only(TypeError, e))


if __name__ == '__main__':
    # non logical 0th order
    json_serializer = JSONSerializer()
    json_deserializer = JSONDeserializer()
    obj_ = [
        logical.parse_logical("A implies B"),
        logical.parse_logical("(C or D) iff (A and (B implies E))"),
        [
            logical.parse_logical("(A iff B) or C")
        ]
    ]
    print("-"*25)
    print(obj_)
    print("-"*25)

    print("Serializing:   ", ser := json_serializer.serialize(obj_))
    try:
        print("Deserializing: ", des := json_deserializer.deserialize(ser))
        print(f"'{des}', and \n'{obj_}' are same? {'yes' if des == obj_ else 'no'}")
    except NotImplementedError:
        pass
