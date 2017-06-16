# Blenbridge
code and docs of the Blenbridge project

Blenbridge is a file conversion app. It is distinctive in the respect that it converts 2D faces
into 3D models. How is this possible? The vertices of the faces are co-located and Blendbridge
exploits this fact. It attempts to make a finite element out of each face, then eliminates a
whole bunch of duplicates. 

Blenbridge could not work without the cooperation of Blender and Blender's export scripts. Blender
is tolerant of the non-manifold meshes that make up the proto-model. (However, not all Blender 
commands will work.) And the Blender .ply export script does not care about the non-manifold nature of
the mesh it exports. (The .obj export script can also function in this respect, but the .ply
format, overall, seems superior.)

The format which Blenbridge writes is legacy .vtk. This format is available in two important
adjunct apps, Paraview and Gmsh. Using all four of the central apps, finite element mesh can be
systematically created with Blender.

Blenbridge is written in Object Pascal, using Lazarus. The current version was compiled under
Lazarus 1.6.


