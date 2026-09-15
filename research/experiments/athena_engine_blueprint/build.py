"""Build the engine reading diagram from the existing contact-geometry specimen.
The geometry is a diagrammatic support, not the trained native topology. All operator
labels and assembly contracts are maintained in docs/ATHENA_ENGINE_BLUEPRINT.md.
"""
from pathlib import Path
import json
import sys
HERE=Path(__file__).resolve().parent
source=json.loads((HERE.parent/'hnn_field_architecture/geometry.json').read_text())
data={key:source[key] for key in ['regions','patches'] if key in source}
# Keep only the contact geometry. The old receiver/three-ray simulation is not this engine.
text=(HERE/'explorer.template.html').read_text().replace('@@DATA@@',json.dumps(data,separators=(',',':')))
output=Path(sys.argv[1]);output.parent.mkdir(parents=True,exist_ok=True);output.write_text(text)
print(output)
