"""Require the complete selected namespace in the actual first Lean root."""
from pathlib import Path
def verify_namespace_lookup(sealed):
    roots=[Path(p) for p in sealed['object_lookup_roots']]
    for row in sealed['modules']:
        if row['module']==sealed['target']:
            continue
        name=row['module']
        prefix=name.split('.')[0]
        candidates=[root for root in roots if (root/prefix).is_dir() or
                    (root/(prefix+'.olean')).is_file()]
        assert candidates, ('no namespace root',name)
        actual=candidates[0]/Path(*name.split('.')).with_suffix('.olean')
        assert actual.is_file(), ('first namespace lacks module',name,str(actual))
        assert str(actual)==row['selected_olean_path'], ('namespace/file lookup differs',name,
                                                      str(actual),row['selected_olean_path'])
