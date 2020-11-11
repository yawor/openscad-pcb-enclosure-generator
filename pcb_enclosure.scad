/*
    PCB Enclosure Generator Module v1.0

    Copyright © 2020 Marcin Jaworski

    This program is free software: you can redistribute it and/or modify
    it under the terms of the GNU General Public License as published by
    the Free Software Foundation, either version 3 of the License, or
    (at your option) any later version.

    This program is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
    GNU General Public License for more details.

    You should have received a copy of the GNU General Public License
    along with this program.  If not, see <http://www.gnu.org/licenses/>
*/

// Main PCB Enclosure Generator module.
// All arguments describing positions of some features take values which are relative to the upper front left corner of the PCB. This means that Z axis values for element positions which are below the PCB should be measured from the top of the board.
// Arguments:
//  pcbDimensions: [x, y, z]: Defines length (x axis), width (y axis) and thickness (z axis) of the PCB (not including any components on the board itself) - it is the only required argument.
//  pcbComponentsBB: [[x1, y1, z1], [x2, y2, z2]]: Two opposite points of a bounding box containing all components on the PCB which have to be included inside the enclosure.
//  mountPosts: a vector of any size of [[x, y], diameter]: Center position and diameter of all mounting posts (or mounting holes in the PCB). The diameter must fit inside the mounting hole of PCB.
//  mountPostsRestrictions: a vector of any size of [[x1, y1, z1], [x2, y2, z2]]: Defines a list of bounding boxes with a restricted space, where mounting posts would collide with some component.
//  mountPostsBaseThicknessOffset: number: Offset which is added to each mounting post's radius below and above the board. It creates a plane on which the board lies.
//  slots: a vector of any size of [side, [a1, b1], [a2, b2]]: A list of slots in the enclosure, where:
//      side: One of "left", "right", "front", "rear", "top", "bottom".
//      [a1, b1], [a2, b2]: Coordinates of points which define rectangles on the surface of the enclosure, where the slots need to be cut. The axes depend on the side of the slot: for left and right a is y, b is z; for front and rear a is x, b is z; for top and bottom a is x, b is y.
//  buttons: a vector of any size of [[x, y], h, angle]: A list of buttons on the top of the enclosure, where:
//      [x, y]: Center position of a button on top of the PCB.
//      h: Height of a released button on the PCB.
//      angle: Rotation of the button cutout around the [x, y].
//  buttonDiameter: number: A diameter of the main part of enclosure buttons.
//  buttonHingeDimensions: [x, y]: Length and width of hinges of enclosure buttons.
//  buttonActuatorDiameter: number: A diameter of the actuator cylinder which connects enclosure button with the PCB one.
//  pcbOffset: number: Extra space between the board and inner side of the enclosure walls. It is calculated from the most protruding feature on each direction.
//  wallThickness: number: Thickness off all 6 walls of the enclosure.
//  tolerance: number: Adds extra distance between some enclosure elements.
//  buttonTolerance: number: A width of the cutout around buttons.
//  outerCornerRadius: number: A radius of the outer enclosure corners.
//  innerCornerRadius: number: A radius of the inner enclosure corners.
//  lipHeight: number: Hight of a lip on the bottom part of the enclosure.
//  topTexts: a vector of any size of [[x, y], text, font, size, halign, valign, angle]: A list of texts (embossed on the top surface + printed inserts) on the top surface of the enclosure, where:
//      [x, y]: Position of a text on the top surface of the enclosure (depends on the halign and valign).
//      text, font, size, halign, valign: parameters of the text as in OpenSCAD documentation.
//      angle: Rotates the text around [x, y].
//  textDepth: number: A depth of the texts on the top surface of the enclosure.
//  assembled: boolean: If true, renders the assembled enclosure, otherwise renders each part separately. Set to false for exporting to STL.
//  export: one of "all", "top", "bottom", "texts": Selects which part to render if assembled is set to false:
//      "all": Renders all the parts
//      "top": Renders only the top part of the enclosure.
//      "bottom": Renders only the bottom part of the enclosure.
//      "texts": Renders only the text inserts to be glued in on top of the enclosure.

module PCBEnclosure(pcbDimensions, pcbComponentsBB=[[0, 0, 0], [0, 0, 0]], mountPosts=[], mountPostsRestrictions=[], mountPostsBaseThicknessOffset=1, slots=[], buttons=[], buttonDiameter=10, buttonHingeDimensions=[3, 2], buttonActuatorDiameter=3, pcbOffset=1, wallThickness=2.0, tolerance=0.4, buttonTolerance=0.2, outerCornerRadius=2, innerCornerRadius=1, lipHeight=2.4, topTexts=[], textDepth=0.4, assembled=false, export="all") {
    
    function toVec(value, length=3) = [for (i = [0:length - 1]) value];
    function addScalar(vec, value) = [for (x = vec) x + value];
    function ensureVecLength(vec, length, value=1) = [for (i = [0:length - 1]) i < len(vec) ? vec[i] : value];
    function vecMin(vects) = let (l = min([for (v = vects) len(v)])) [for (i = [0:len(vects[0]) - 1]) min([for (v = vects) v[i]])];
    function vecMax(vects) = let (l = min([for (v = vects) len(v)])) [for (i = [0:len(vects[0]) - 1]) max([for (v = vects) v[i]])];
    function vecReplace(vec, rep) = [for (i = [0:len(vec) - 1]) let (s = search(i, rep)[0]) s == undef ? vec[i] : rep[s][1]];
    function select(vector, indices) = [for (index = indices) vector[index]];

    function isLeftRight(slot) = (slot[0] == "left" || slot[0] == "right");
    function isFrontRear(slot) = (slot[0] == "front" || slot[0] == "rear");
    function isSide(slot) = (isLeftRight(slot) || isFrontRear(slot));
    function isTopBottom(slot) = (slot[0] == "top" || slot[0] == "bottom");

    function getBB(vects=[[0, 0, 0], [1, 1, 1]], axes="xyz", x1=undef, y1=undef, z1=undef, x2=undef, y2=undef, z2=undef, dx1=0, dy1=0, dz1=0, dx2=0, dy2=0, dz2=0) = let (xIdx = search("x", axes)[0], yIdx = search("y", axes)[0], zIdx = search("z", axes)[0])
        let (minv = vecMin(vects), maxv = vecMax(vects))
        let (v1 = [
            (x1 != undef ? x1 : xIdx != undef ? minv[xIdx] : 0) + dx1,
            (y1 != undef ? y1 : yIdx != undef ? minv[yIdx] : 0) + dy1,
            (z1 != undef ? z1 : zIdx != undef ? minv[zIdx] : 0) + dz1,
        ], v2 = [
            (x2 != undef ? x2 : xIdx != undef ? maxv[xIdx] : 0) + dx2,
            (y2 != undef ? y2 : yIdx != undef ? maxv[yIdx] : 0) + dy2,
            (z2 != undef ? z2 : zIdx != undef ? maxv[zIdx] : 0) + dz2
        ]) [v1, v2 - v1];
    
    function _getSlotBBXY(slotbb, offs, thickness) =
        getBB(slotbb, axes="xy", z1=min(offs, offs + thickness), z2=max(offs, offs + thickness));
    function _getSlotBBXZ(slotbb, offs, thickness) =
        getBB(slotbb, axes="xz", y1=min(offs, offs + thickness), y2=max(offs, offs + thickness));
    function _getSlotBBYZ(slotbb, offs, thickness) =
        getBB(slotbb, axes="yz", x1=min(offs, offs + thickness), x2=max(offs, offs + thickness));
    
    function getSlotBB(slot, offsets, thickness) =
        let (
            bb = select(slot, [1, 2]),
            axes = isLeftRight(slot) ? "yz"
                : isFrontRear(slot) ? "xz"
                : "xy",
            offs = slot[0] == "left" ? offsets[0][0]
                : slot[0] == "front" ? offsets[0][1]
                : slot[0] == "bottom" ? offsets[0][2]
                : slot[0] == "right" ? offsets[1][0]
                : slot[0] == "rear" ? offsets[1][1]
                : offsets[1][2]
        ) axes == "yz" ? _getSlotBBYZ(bb, offs, thickness)
            : axes == "xz" ? _getSlotBBXZ(bb, offs, thickness)
            : _getSlotBBXY(bb, offs, thickness);

    boardBB = let(compBB = getBB(pcbComponentsBB), slotsBBs = [for (s = slots) getSlotBB(s, [[0, 0, 0], vecReplace(pcbDimensions, [[2, 0]])], 0)], allDim = concat([pcbDimensions, compBB[0], compBB[0] + compBB[1]], [for (slot = slotsBBs) each [slot[0], slot[0] + slot[1]]])) [vecMin(allDim), vecMax(allDim)];

    boardDim = boardBB[1] - boardBB[0];

    innerDim = addScalar(boardDim, 2 * pcbOffset);
    outerDim = addScalar(innerDim, 2 * wallThickness);
    
    pcbLoc = addScalar(boardBB[0] * -1, pcbOffset + wallThickness);
    slotOffsets = [
        addScalar([0, 0, boardBB[0].z], -(wallThickness + pcbOffset)),
        vecReplace(addScalar(innerDim, -pcbOffset), [[2, boardBB[1].z + pcbOffset]])
    ];
    
    if (assembled) {
        Top();
    } else if (export == "top") {
        Top(true);
    } else if (export == "all") {
        translate([0, outerDim.y + 5]) Top(true);
        translate([outerDim.x + 5, 0]) TextsArray();
    } else if (export == "texts") {
        TextsArray();
    }
    
    if (assembled || export == "all" || export == "bottom") {
        Bottom();
    }
    
    module RoundedCube(v, r=1) {
        v1 = addScalar(ensureVecLength(v, 3), -2 * r);
        
        translate(toVec(r)) hull() for (x = [0, v1.x], y = [0, v1.y], z = [0, v1.z]) {
            translate([x, y, z]) sphere(r / cos(180 / $fn));
        }
    }
    
    module AtPCB(x=undef, y=undef, z=undef) {
        v = vecReplace(pcbLoc, concat(
            x != undef ? [[0, x]] : [],
            y != undef ? [[1, y]] : [],
            z != undef ? [[2, z]] : []
        ));
        translate(v) children();
    }
    
    module Top(forExport=false) {
        module part() {
            union() {
                difference() {
                    intersection() {
                        Base();
                        TopBottomCut("top");
                    }
                    translate([0, 0, -0.01]) Lip(lipHeight + 0.01, tolerance / 2, tolerance / 8);
                    
                    AtPCB() Slots(slots, "top", true);
                    
                    AtPCB(z=outerDim.z - textDepth) TextsArray(tolerance / 2);
                    
                    AtPCB(z=outerDim.z - wallThickness) ButtonsArray(true);
                }
                AtPCB() Slots(slots, "top", false);
                AtPCB() Posts("top");
                AtPCB() ButtonsArray();
            }
        }
        
        if (forExport) {
            translate([outerDim.x, 0, outerDim.z]) rotate([0, 180, 0]) part();
        } else {
            part();
        }
    }
    
    module Bottom() {
        union() {
            difference() {
                union() {
                    intersection() {
                        Base();
                        TopBottomCut("bottom");
                    }
                    Lip(lipHeight, -tolerance / 2, -tolerance / 8);
                }
                
                AtPCB() Slots(slots, "bottom", true);
            }
            AtPCB() Slots(slots, "bottom", false);

            AtPCB() Posts("bottom");

        }
    }
    
    module TextsArray(offs=0, negative=false) {
        for (tdef = topTexts) {
            translate(tdef[0]) linear_extrude(textDepth + 0.01) offset(offs) Text(tdef);
        }
    }
    
    module Slots(slots, part, negative=false) {
        offsets = negative ? slotOffsets - [toVec(0.01), toVec(0.01)] : slotOffsets;
        wt = negative ? wallThickness + 0.02 : wallThickness;
        
        for (slot = slots) {
            bb = getSlotBB(slot, offsets, wt);
            p1 = negative ? bb[0]
                : isLeftRight(slot) ? vecReplace(bb[0], [[1, bb[0].y + tolerance]])
                : isFrontRear(slot) ? vecReplace(bb[0], [[0, bb[0].x + tolerance]])
                : bb[0];
            s = negative ? bb[1]
                : isLeftRight(slot) ? vecReplace(bb[1], [[1, bb[1].y - tolerance * 2]])
                : isFrontRear(slot) ? vecReplace(bb[1], [[0, bb[1].x - tolerance * 2]])
                : bb[1];

            p2 = p1 + s;
            
            if (negative && isTopBottom(slot)) {
                translate(p1) cube(s);
            } else if (part == "bottom") {
                if (negative) {
                    if (isSide(slot) && p1.z < lipHeight) {
                        translate(p1) cube(vecReplace(s, [[2, lipHeight + s.z - p2.z + 0.01]]));
                    }
                } else {
                    if (isSide(slot) && p1.z > 0) {
                        translate(vecReplace(p1, [[2, 0]])) cube(vecReplace(s, [[2, p1.z]]));
                    }
                }
            } else if (part == "top") {
                if (negative) {
                    if (isSide(slot) && p2.z > 0) {
                        translate(vecReplace(p1, [[2, -0.01]])) cube(vecReplace(s, [[2, p2.z]]));
                    }
                } else {
                    if (isSide(slot) && p2.z < lipHeight) {
                        translate(vecReplace(p1, [[2, p2.z]])) cube(vecReplace(s, [[2, -p2.z + lipHeight]]));
                    }
                }
            }
        }
    }
    
    module TopBottomCut(part) {
        v1 = part == "bottom" ? toVec(0) : [0, 0, pcbLoc.z];
        h = part == "bottom" ? pcbLoc.z : outerDim.z - pcbLoc.z;
        translate(v1) cube(vecReplace(outerDim, [[2, h]]));
    }
    
    module Lip(height, offs, snapOffs=0) {
        module RoundedFlat(vec, r) {
            v = addScalar(vec, -2 * r);
            translate(toVec(r, 2)) hull() for (x = [0, v.x], y = [0, v.y]) {
                translate([x, y]) circle(r);
            }
        }
        
        module Snap(l, w, h) {
            rotate([-90, 0, -90]) linear_extrude(l) polygon([[0, -h / 2], [0, h / 2], [w, 0]]);
        }
        
        thickness = wallThickness / 2 + offs;
        
        snapB = wallThickness / 4;
        snapW = wallThickness / 2;
        snapH = lipHeight;
        
        translate([wallThickness, wallThickness, pcbLoc.z - 0.02]) {
            linear_extrude(height + 0.02) difference() {
                offset(thickness) RoundedFlat(innerDim, innerCornerRadius);
                RoundedFlat(innerDim, innerCornerRadius);
            }
            
            translate([0, 0, lipHeight - snapH / 2 + 0.02]) {
                translate([innerCornerRadius * 2, - snapB - snapOffs]) Snap(innerDim.x - innerCornerRadius * 4, snapW, snapH);
                translate([innerCornerRadius * 2, snapB + innerDim.y + snapOffs]) mirror([0, 1]) Snap(innerDim.x - innerCornerRadius * 4, snapW, snapH);
                translate([-snapB - snapOffs, innerCornerRadius * 2]) rotate([180, 0, 90]) Snap(innerDim.y - innerCornerRadius * 4, snapW, snapH);
                translate([snapB + innerDim.x + snapOffs, innerCornerRadius * 2]) mirror([1, 0]) rotate([180, 0, 90]) Snap(innerDim.y - innerCornerRadius * 4, snapW, snapH);
            }
        }
    }
    
    module Posts(part) {
        difference() {
            for (post = mountPosts) {
                translate(post[0]) {
                    if (part == "top") {
                        difference() {
                            cylinder(r=post[1] / 2 + mountPostsBaseThicknessOffset, h=outerDim.z - pcbLoc.z - wallThickness + 0.03);
                            translate([0, 0, -0.01]) cylinder(r=(post[1] + tolerance) / 2, h=lipHeight + tolerance / 2 + 0.01);
                        }
                    } else {
                        translate([0, 0, -pcbLoc.z]) cylinder(r=post[1] / 2 + mountPostsBaseThicknessOffset, h=pcbLoc.z - pcbDimensions.z);
                        translate([0, 0, -pcbDimensions.z]) cylinder(r=(post[1] - tolerance) / 2, h=pcbDimensions.z + lipHeight - tolerance / 2);
                    }
                }
            }
            
            for (area = mountPostsRestrictions) {
                bb = getBB(area);
                translate(bb[0]) cube(bb[1]);
            }
        }
    }
    
    module Text(tdef) {
        rotate([0, 0, tdef[6]]) text(text=tdef[1], font=tdef[2], size=tdef[3], halign=tdef[4], valign=tdef[5]);
    }
    
    module ButtonsArray(negative=false) {
        module ButtonProfile(r, hingeDim) {
            circle(r);
            translate([0, -hingeDim.y / 2]) square([hingeDim.x + r, hingeDim.y]);
        }
        
        for (button = buttons) {
            pos = button[0];
            translate([pos.x, pos.y, -0.01]) if (negative) {
                rotate([0, 0, button[2]]) translate([buttonDiameter / 2 - buttonActuatorDiameter / 2 - buttonTolerance, 0, 0]) {
                    linear_extrude(wallThickness + 0.02) difference() {
                        ButtonProfile(buttonDiameter / 2, buttonHingeDimensions);
                        offset(-buttonTolerance) ButtonProfile(buttonDiameter / 2, [buttonHingeDimensions.x + buttonTolerance, buttonHingeDimensions.y]);
                    }
                    translate([buttonDiameter / 2 + buttonHingeDimensions.x - wallThickness / 2, 0]) rotate([90, 0, 0]) cylinder(r=wallThickness / 2, h=buttonHingeDimensions.y, center=true);
                }
            } else {
                translate([0, 0, button[1]]) cylinder(r=buttonActuatorDiameter / 2, h=outerDim.z - wallThickness - pcbLoc.z - button[1] + 0.03);
            }
        }
    }
    
    module Base() {
        difference() {
            RoundedCube(outerDim, r=outerCornerRadius);
            translate(toVec(wallThickness)) RoundedCube(innerDim, r=innerCornerRadius);
        }
    }
}
