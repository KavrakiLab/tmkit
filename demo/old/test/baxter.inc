
#include "colors.inc"    // The include files contain
#include "stones.inc"    // pre-defined scene elements

#include "textures.inc"    // pre-defined scene elements
#include "shapes.inc"
#include "glass.inc"
#include "metals.inc"
#include "woods.inc"
#include "skies.inc"


#declare Black_Marble_Map =
color_map {
    [0.0 rgb <0.0, 0.0, 0.0>]
    [0.8 rgb <0.1, 0.1, 0.1>]
    [1.0 rgb <0.3, 0.3, 0.3>]
}

// Black marble with black veins.
#declare Black_Marble =
pigment {
    marble
    turbulence 2
    color_map { Black_Marble_Map }
}


camera {
  //location <2.25, 1.0, 0.5>
//  location <1.5, 1.5, 2.0>
  location <1.75, 1.25, 0.75>
  look_at  <0,    .0,  0>
  right x*16/9 /* Widescreen */
}

#include "stars.inc"
sky_sphere{ //<0,0,0>, 1
  //S_Cloud3
  pigment {
    //Blood_Sky
    //Blue_Sky
    White
 //   Apocalypse
  }


  scale 0.3
  rotate <0,3,3>
}

// box {

//     <-2.54,0,-2.54>,  // Near lower left corner
//     < 2.54, 0, 2.54>   // Far upper right corner
// plane { <0, 1, 0>, 0
//   //texture {

//     //pigment{ color rgb<0.22,0.45,0>}
//     //normal { bumps 0.75 scale 0.015 }
//     //finish { phong 0.1 }
//     //} // end of texture

//   texture {
//     pigment
//     {
//       checker pigment { Black_Marble }, pigment { White_Marble }
//       scale 12*0.0254
//       //checker color Black, color White
//     }
//     //finish{ phong 0.5 }
//   }
//   translate <0,-.9,0>

// }

// box {
//     <0,0,0>  // Near lower left corner
//     < .5, 1.5, .5>   // Far upper right corner
//     material {M_Water}
//     texture {
//     Vicks_Bottle_Glass
//     finish {ambient .2}
//     }
// }


// light_source {
//   <5, 1, 5>
//   color White
//   area_light <5, 0, 0>, <0, 0, 5>, 5, 5
//   point_at <0, 0, 0>
//   adaptive 1
//   fade_distance 8 fade_power 2
// }

 // light_source {
 //    <2, 2, 2>
 //    color White
 //    spotlight
 //    radius 3
 //    //falloff 18
 //    tightness 10
 //    area_light <1, 0, 0>, <0, 0, 1>, 2, 2
 //    adaptive 1
 //    jitter
 //    point_at <0, 0, 0>
 //  }

// box {
//     <-1.01,-1.1,-1.9>  // Near lower left corner
//     <-1.01, 1.1,1.9>   // Far upper right corner
//   texture {
//     T_Wood8

//     scale 0.254
//   }
// }


/////////////
// MIRRORS //
/////////////

// box {
//   <0, 0,   1.1>  // Near lower left corner
//   <0, 2, -1.1 >   // Far upper right corner
//   texture{
//     T_Wood8
//     scale 0.254
//   }
//   translate <-1.001,-.9,.75>
//   rotate 20*y
// }

// box {
//   <0, .1, 1>  // Near lower left corner
//   <0, 1.9, -1 >   // Far upper right corner
//   texture{ Polished_Chrome }
//   translate <-1,-.9,.75>
//   rotate 20*y
// }

// box {
//   <0, 0,   1.1>  // Near lower left corner
//   <0, 2, -1.1 >   // Far upper right corner
//   texture{
//     T_Wood8
//     scale 0.254
//   }
//   translate <-1.001,-.9,-.75>
//   rotate -20*y
// }

// box {
//   <0, .1, 1>  // Near lower left corner
//   <0, 1.9, -1 >   // Far upper right corner
//   texture{ Polished_Chrome }
//   translate <-1,-.9,-.75>
//   rotate -20*y
// }



global_settings { ambient_light rgb<.75, .75, .75> }
light_source{<10,20,15>
  // Sun
  color White
  parallel
  jitter
  adaptive 1
}

 // light_source {
 //    <2, 5, 0>
 //    color White
 //    spotlight

 //    radius 1
 //    //falloff 18
 //    tightness 60
 //    area_light <.5, 0, 0>, <0, 0, .5>, 1, 1
 //    //adaptive 1
 //    jitter
 //    point_at <0, 0, 0>
 //   fade_distance 4 fade_power 2
 // }

// light_source
// {
//   <5, 5, 0>
//   color White
//   fade_distance 3 fade_power 2
//   jitter
//   area_light x*3, y*3, 12, 12 circular orient adaptive 0
// }

// light_source
// {
//   <5, 5, -5>
//   color White
//   fade_distance 3 fade_power 2
//   jitter
//   area_light x*3, y*3, 12, 12 circular orient adaptive 0
// }

// light_source {
//   <10, 5, -5>
//   color White
//   area_light <5, 0, 0>, <0, 0, 5>, 5, 5
//   adaptive 1
//   fade_distance 8 fade_power 2
// }


// fog {
//   fog_type   2
//   distance   0
//   color      rgb<1,1,1>*0.8
//   fog_offset .1
//   fog_alt    0
//   turbulence 0
// } //
