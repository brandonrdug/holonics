#import "lib.typ": engrave
#let sample=(bounds:(0,0,2,1),marks:((points:((0,0),(2,1)),rgb:(1,0,0),width:1,kind:"hatch"),(points:((1,1/2),),rgb:(0,1,0),width:2,kind:"stipple")),meta:(:))
#set page(width:100mm,height:60mm,margin:5mm)
#context {
 let drawing=engrave(sample,width:40mm,height:40mm)
 let size=measure(drawing)
 assert(size.width==40mm and size.height==40mm,message:"explicit viewport fit must retain its declared block extent")
 drawing
}
