#import "lib.typ": engrave
#let scenes=json("../../papers/hnn-information-chemistry/receiver-scenes.json")
#set page(width:190mm,height:150mm,margin:5mm,fill:white)
#grid(columns:(1fr,1fr),gutter:5mm,
 [Typst packet\ #engrave(scenes.shorts_phase,width:84mm)],
 [SVG packet\ #image("../../../rendered/receiver-engraving/shorts_phase.svg",width:84mm)],
)
