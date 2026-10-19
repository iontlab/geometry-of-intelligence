"""Shared learning registry policy; byte counts refer to serialized UTF-8."""
import hashlib, json
from pathlib import Path
PATH=Path(__file__).resolve().parents[1]/'docs/formalization/mathematics-learning/explanations/capacity.json'
def capacity():
    raw=PATH.read_bytes()
    assert len(raw)<=4096, 'Capacity configuration too large'
    c=json.loads(raw)
    assert c.get('schema_version')=='learning-capacity-1'
    for key,lo,hi in [('registry_bytes',500000,50000000),('registry_records',200,100000)]:
        assert type(c.get(key)) is int and lo<=c[key]<=hi, key
    return c
def check_registry(raw):
    c=capacity()
    assert len(raw)<=c['registry_bytes'], 'Registry capacity exceeded'
    assert len(json.loads(raw)['records'])<=c['registry_records'], 'Registry record capacity exceeded'
    return c['registry_bytes']-len(raw)
def capacity_hash():
    capacity()
    return hashlib.sha256(PATH.read_bytes()).hexdigest()
