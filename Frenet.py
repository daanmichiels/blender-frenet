bl_info = {
 "name": "Frenet",
 "author": "Daan Michiels",
 "version": (0, 1),
 "blender": (2, 66, 0),
 "location": "View3D > Object > Frenetify curve",
 "description": "Calculates the Frenet frame of a smoothened version of the active Bezier curve. The smoothened version will be inserted as a polyline. The Bezier frame will be added as empties, which are keyframed over the length of the curve at unit speed.",
 "warning": "",
 "wiki_url": "",
 "tracker_url": "",
 "category": "Object"}

'''
This module provides functionality in Blender to calculate the Frenet frame of
(a smooth approximation of) a Bezier spline.
'''

#debugging, performance testing
#import sys
#import time
import bpy
from math import sqrt, fsum, modf, floor
from mathutils import Vector

def dist(p,q):
    t = [p[i]-q[i] for i in range(len(p))]
    t = [x*x for x in t]
    return sqrt(fsum(t))

def cross_product(p,q):
    return [p[1]*q[2]-p[2]*q[1], p[2]*q[0]-p[0]*q[2], p[0]*q[1]-p[1]*q[0]]

def normalize(p):
    norm = dist(p,[0,0,0])
    return [x/norm for x in p]

def search_float(l,x):
    """
    Performs a search on an increasing list l of floats,
    looking for the two consecutive values enclosing the float x.
    If x is smaller than the minimum of l, returns 0.0.
    If x is greater than the maximum of l, returns 1.0.
    If x is found in l, returns the average of the first and last
    index at which x is located.
    If x is strictly enclosed between l[i] and l[i+1], returns
    a linearly interpolated version of i and (i+1), corresponding to
    weighed by how close x is to l[i] and l[i+1].
    It is given by
         i + (x-l[i])/(l[i+1]-l[i]).
    The implementation is not geared towards performance.
    By the way: if len(l) is less than one, just returns.
    """

    if len(l)<1:
        return
    if len(l)==1:
        return 0.0
    if x<l[0]:
        return 0.0
    if x>l[-1]:
        return len(l)-1.0

    atleastx = [(y>=x) for y in l]
    atmostx = [(y<=x) for y in l]

    #find first position of stuff that is at least x
    a = atleastx.index(True)
    #find last position of stuff that is at most x
    #this is slightly more complicated, because there is no
    #'last occurrence'-function
    if atmostx[-1]:
        b = len(l)-1
    else:
        b = atmostx.index(False)-1

    if a<=b: #x is found
        return (a+b)/2.0

    #x is not found
    assert a==b+1
    assert x<l[a]
    assert x>l[b]

    return b + float(x-l[b])/(l[a]-l[b])

class BezierCurve:
    """
    A bezier curve, stored as a list of control points.
    It also keeps a lookup table of arc lengths corresponding to
    regularly-spaced time values, that is overwritten whenever a more
    detailed lookup table is required for the calculations than the one
    already stored.
    Note that some of the methods in this class may give wrong results if any of the control points
    have changed since the last time the lookup table was built.
    To ensure correct results, you can call clear_lookup() first.
    All methods that use the lookup table have explicit mention of this
    in their docstring.
    """
    def __init__(self, c = [[0.0,0.0,0.0]]):
        if len(c)>=1:
            self.control_points = c
        else:
            self.control_points = [[0.0,0.0,0.0]]
        self.partial_lengths = []
    
    def clear_lookup(self):
        self.partial_lengths = []
    
    def dim(self):
        #naive implementation
        #there is no enforcing of all points having equal length, but hey
        return len(self.control_points[0])
    
    def degree(self):
        return len(self.control_points)-1
    
    def at_t(self, t):
        """
        Evaluates the Bezier curve at time t (between 0 and 1)
        using De Casteljau's algorithm.
        """
        if len(self.control_points) < 1:
            return
        temp = self.control_points
        while len(temp) > 1:
            temp = [[(1-t)*temp[i][j] + t*temp[i+1][j] for j in range(len(temp[i])) ] for i in range(len(temp)-1)]
        return temp[0]
    
    def increase_degree(self):
        """
        Returns a Bezier curve with identical shape but
        of one degree higher.
        """
        new_control_points = [self.control_points[0]]
        n = len(self.control_points)-1
        for i in range(len(self.control_points)-1):
            a = float(i+1)/(n+1)
            b = 1-a
            new_control_point = [a*self.control_points[i][j]+b*self.control_points[i+1][j] for j in range(len(self.control_points[0]))]
            new_control_points.append(new_control_point)
        new_control_points.append(self.control_points[-1])
        return BezierCurve(new_control_points)

    def approx_length(self, lower=0.0, upper=1.0, minsteps=1000):
        """
        Approximates the length of the Bezier curve between two given times.

        If lower!=0.0 or upper!=1.0, no use is made of the lookup table,
        and the timespan is divided into minsteps pieces.
        The resulting minsteps+1 points will be calculated, and the distances
        of the minsteps segments between them summed.
        This gives the approximation.

        If lower==0.0 and upper==1.0, then use is made of the lookup table
        if this contains at least minsteps+1 points (so that it was based on
        at least minsteps steps).
        Otherwise, the unit interval is divided into minsteps pieces.
        The resulting minsteps+1 points will be calculated, and the distance
        of the minsteps segments between them summed.
        This gives the approximation.
        Furthermore, the old lookup table will be overwritten by this new,
        more detailed one.
        """
        if lower==0.0 and upper==1.0 and len(self.partial_lengths)>minsteps:
            return self.partial_lengths[-1]

        times = [lower+i*float(upper-lower)/minsteps for i in range(minsteps+1)]
        points = [self.at_t(t) for t in times]
        lengths = [dist(points[i], points[i+1]) for i in range(minsteps)]
        partials = [0.0] * (minsteps+1)
        for i in range(len(lengths)):
            partials[i+1] = partials[i]+lengths[i]

        #if the newly calculated list of intermediate lengths
        #is more detailed than the previous one,
        #store the new one
        if lower==0.0 and upper==1.0 and len(partials)>len(self.partial_lengths):
            self.partial_lengths = partials
        return partials[-1] #last element of list

    def t_to_s(self, t, minsteps=1000):
        """
        Approximates the arc length of the curve from time 0.0 to t
        using minsteps intervals.
        This is a simple call to approx_length.
        In particular, if this is called with t==1.0, it will force
        the lookup table to be updated if minsteps is high enough.
        Note that in particular the value for t==1.0 may be based
        on a much finer approximation that the one for other times
        (given equal minsteps), if previously a big lookup table was constructed.
        """
        return self.approx_length(lower=0.0, upper=t, minsteps=minsteps)

    def s_to_t(self, s, minsteps=1000):
        """
        Approximates the time corresponding to a given arc length.
        This is done using a lookup in the lookup table of arc lengths
        that is calculated for equally spaced times, and linearly interpolated
        between the enclosing arc lengths found in the table.
        If the given s is not on the curve, it will be clamped first.
        The minsteps parameter gives control over the accuracy of the
        approximation by requiring that the lookup table uses at least minsteps
        steps (has at least minsteps+1 entries).
        If the current lookup table is not big enough, it will be calculated
        by a call to approx_length.
        """
        if len(self.partial_lengths)<minsteps+1:
            self.approx_length(minsteps=minsteps)

        index = search_float(self.partial_lengths, s)
        return index * 1.0/(len(self.partial_lengths)-1)
    
    def at_s(self, s, minsteps=1000):
        """
        Gives the point on the curve at arc length s.
        This is a call to s_to_t followed by a call to at_t,
        passing minsteps along.
        Note that this may use the lookup table.
        """
        return self.at_t(self.s_to_t(s, minsteps=minsteps))
    
    def diff(self):
        """
        Differentiates the given Bezier curve.
        The result is a Bezier curve of one degree lower,
        or the zero curve (of degree 0) if the curve has degree 0.
        """
        if self.degree()==0:
            return BezierCurve([[0.0]*self.dim()])

        #based on http://www.cs.mtu.edu/~shene/COURSES/cs3621/NOTES/spline/Bezier/bezier-der.html
        n = len(self.control_points)
        diff_control_points = [[n*(self.control_points[i+1][j] - self.control_points[i][j]) for j in range(self.dim())] for i in range(n-1)]
        return BezierCurve(diff_control_points)

class BezierSpline:
    """
    A Bezier spline, which is essentially a list of Bezier curves.
    It is parametrized by a time parameter t = i.f with i the integer part
    and f the fractional part of t. This corresponds to time f on curve i.
    """
    def __init__(self, curves = []):
        self.curves = curves
        self.partial_lengths = []
        self.steps_used = 0

    def clear_lookup(self, clear_curves_lookup = False):
        """
        Clears all stored lookup data of the spline.
        If clear_curves_lookup is True, then also the lookup data
        off all underlying curves is cleared.
        """
        self.partial_lengths = []
        self.steps_used = 0
        if clear_curves_lookup:
            for c in self.curves:
                c.clear_lookup()
    
    def increase_degree(self):
        curves = [c.increase_degree() for c in self.curves]
        return BezierSpline(curves)

    def at_t(self,t):
        """
        Evaluates the spline at the given time.
        If t is integer, so that it corresponds to the end point of
        some curve and to the start of another, return the start of
        the latter curve.
        If t is out of range, it will be clamped.
        """
        if t<0.0:
            t = 0.0
        f, i = modf(t)
        i = int(i)
        if i>=len(self.curves):
            i = len(self.curves)-1
            f = 1.0
        return self.curves[i].at_t(f)

    def t_to_s(self,t,minsteps=1000):
        """
        Approximates the arc length of the spline from t=0.0 to
        the given time.
        All curves that are encountered will use arc length approximations
        with the given number of steps.
        """
        if t<0.0:
            t = 0.0
        f, i = modf(t)
        i = int(i)
        if i>=len(self.curves):
            i = len(self.curves)-1
            f = 1.0

        total_s = 0.0
        if i>0:
            for c in self.curves[:i]:
              total_s = total_s + c.approx_length(minsteps=minsteps)
        total_s = total_s + self.curves[i].approx_length(upper=f, minsteps=minsteps)
        return total_s

    def s_to_t(self,s,minsteps=1000):
        i = 0
        length = self.curves[i].approx_length(minsteps=minsteps)
        while s>length:
            s = s-length
            i = i+1
            if i>=len(self.curves):
                return len(self.curves)
            length = self.curves[i].approx_length(minsteps=minsteps)

        return i + self.curves[i].s_to_t(s,minsteps=minsteps)

    #todo: implement lower and upper
    def approx_length(self, minsteps = 1000):
        """
        Calculates the length of the Bezier spline, which is
        just the sum of the approx_length's of the curves.
        The parameter steps is passed to approx_length of each individual curve.
        """
        if len(self.curves)==0:
            return 0.0
        n = len(self.curves)

        lengths = [c.approx_length(minsteps=minsteps) for c in self.curves]
        partials = [0.0] * (n+1)
        for i in range(n):
            partials[i+1] = partials[i]+lengths[i]

        #if the newly calculated list of intermediate lengths
        #is more detailed than the previous one,
        #store the new one
        if len(partials)>len(self.partial_lengths):
            self.partial_lengths = partials

        return partials[-1] #last element of list

    def at_s(self, s, minsteps=1000):
        """
        Gives the point on the curve at arc length s.
        This is a call to s_to_t followed by a call to at_t,
        passing minsteps along.
        """
        return self.at_t(self.s_to_t(s, minsteps=minsteps))

    def diff(self):
        return BezierSpline([c.diff() for c in self.curves])

class FrenetHelper:
    """
    Provides conversions between the custom Bezier-types and the Blender ones,
    and smoothing procedures to make curves C^2.
    """
    def ToBezierSpline(bezier):
        """Convert the first spline in a Blender Bezier curve into a BezierSpline.
           The argument is the object representing the Blender Bezier curve.
           (The relationship between the object encapsulating the curve and the curve
           itself is not completely clear to me yet.)
           """
        print("Converting {} to BezierSpline".format(bezier.name))
        if bezier.type != "CURVE":
            print("Not a curve.")
            return
        bezier = bezier.data.splines[0] #only use the first one
        if bezier.type != "BEZIER":
            print("Not a bezier.")
            return
        curves = []
        for i in range(len(bezier.bezier_points)-1):
            point0 = bezier.bezier_points[i].co
            point1 = bezier.bezier_points[i].handle_right
            point2 = bezier.bezier_points[i+1].handle_left
            point3 = bezier.bezier_points[i+1].co
            curves.append(BezierCurve([point0, point1, point2, point3]))
        return BezierSpline(curves)

    def SolidifyBezierSpline(sp,steps=100,curvename="SolidifiedCurve",objname="SolidifiedObject"):
        poly = bpy.data.curves.new(curvename,'CURVE')
        obj = bpy.data.objects.new(objname, poly)
        spl = poly.splines.new('POLY')
        spl.points.add(steps)
        maxt = len(sp.curves)
        for n in range(steps+1):
            t = n*maxt/float(steps)
            point = sp.at_t(t)
            spl.points[n].co.x = point[0]
            spl.points[n].co.y = point[1]
            spl.points[n].co.z = point[2]
        bpy.context.scene.objects.link(obj)

    def ApproximateByC2(sp):
        """Approximates the given BezierSpline by a BezierSpline that is twice continuously
           differentiable. The resulting BezierSpline is of degree at least 5.

           First, the degree of the BezierSpline is increased until it is at least 5.
           If it already was 5 or more, it is not changed.
           Then, the following procedure is applied:
             - we make the curve C0 (continuous):
               if two consecutive curves do not 'connect',
               we connect them at the average point of the two nodes
             - we make the curve C1:
               we make the control points directly around p such that (handle1-p) is the opposite of (handle2-p)
               we do this in such a way that the sum of the length of the handles is preserved
               and in such a way that handle2-handle1 does not change direction
             - we make the curve C2:
               we move the control points at a distance 2 from p in such a way that the second derivative at p becomes continuous
               we do this such that the average of these two control points does not change (this determines it uniquely)
           This procedure seems reasonable, although admittedly it is ad-hoc.

           If the original BezierSpline has no curves, the original BezierSpline is returned.
           This method assumes that all curves in the given BezierSpline have the same degree and dimension.
           """

        if len(sp.curves)<1:
          return sp
        #increase degree sufficiently
        while sp.curves[0].degree()<5:
          sp = sp.increase_degree()

        dim = sp.curves[0].dim()
        #now repair at every internal node (i.e. every node that is not the first or last one)
        #let i run from 1 to len(sp.curves)-1
        for i in [i+1 for i in range(len(sp.curves)-1)]:
            #we now repair node i (where the first one is numbered 0)
            #call this node p (for point)
            #the procedure is the following:
            #  we make the curve continuous:
            #    if two consecutive curves do not 'connect',
            #    we connect them at the average point of the two nodes
            #  we repair the first derivative:
            #    we make the handles around p such that (handle1-p) is the opposite of (handle2-p)
            #    we do this in such a way that the sum of the length of the handles is preserved
            #    and in such a way that handle2-handle1 does not change direction
            #  we repair the second derivative:
            #    we move the control points at a distance 2 from p in such a way that the second derivative at p becomes continuous
            #    we do this such that the average of these two control points does not change
            #this procedure seems reasonable
            curve_left  = sp.curves[i-1]
            curve_right = sp.curves[i]
            
            #make C^0
            p = [(curve_left.control_points[-1][j]+curve_right.control_points[0][j])/2.0 for j in range(dim)]


            curve_left.control_points[-1] = p
            curve_right.control_points[0] = p
            
            #make C^1
            v = [0.0]*dim
            total_handle_length = dist(p,curve_left.control_points[-2]) + dist(p,curve_right.control_points[1])
            if total_handle_length > 0:
                v = normalize([curve_right.control_points[1][j] - curve_left.control_points[-2][j] for j in range(dim)])
                v = [v[j]*total_handle_length for j in range(dim)]
                curve_left.control_points[-2] = [p[j]-v[j]/2.0 for j in range(dim)]
                curve_right.control_points[1] = [p[j]+v[j]/2.0 for j in range(dim)]
            
            #make C^2
            #we can reuse v from before
            center = [(curve_left.control_points[-3][j]+curve_right.control_points[2][j])/2.0 for j in range(dim)]
            curve_left.control_points[-3] = [center[j]-v[j] for j in range(dim)]
            curve_right.control_points[2] = [center[j]+v[j] for j in range(dim)]
        
        return sp

    def ForceCubicC2(bezier):
        """Forces a Blender bezier spline to be twice continuously differentiable.
           This is done in a single forward pass, which can result in a spline that
           behaves very wildly compared to the one originally supplied.
           In general, it is advised to use ApproximateByC2 instead if possible.

           The argument supplied is the object representing the Blender Bezier curve.
           (The relationship between the object encapsulating the curve and the curve
           itself is not completely clear to me yet.)

           If the supplied spline is already continuous, no nodes will be moved.
           (By a node we mean the outer control points of the curves, i.e. the points
           that the spline goes through with certainty.)
           The first curve in the spline will not be changed. In particular, if 
           the spline contains only a single curve, nothing will be changed.
           Everything else may be changed by this method.

           The first curve is left untouched.
           Starting from the second curve in the spline, the following is applied
           to all curves: (call the first node on the current curve p, and the second q)
             - The right handle of p is moved to make the spline C1 at p.
             - The left handle of q is moved to make the spline C2 at p.

           Only the first spline in the curve object will be considered.
           """
        print("ForceCubicC2 was called (for curve {}). Use of this method is not recommended.".format(bezier.name))
        if bezier.type != "CURVE":
            print("Not a curve.")
            return
        bezier = bezier.data.splines[0] #only use the first one
        if bezier.type != "BEZIER":
            print("Not a bezier.")
            return
        if len(bezier.bezier_points)<3:
            return
        for i in [1+i for i in range(len(bezier.bezier_points)-2)]:
            #adjust the segment between bezier_points[i] and bezier_points[i+1]
            #using the control points of the segment between bezier_points[i-1] and bezier_points[i]
            #these formulas look long and ugly, so maybe improve this a bit sometime
            bezier.bezier_points[i].handle_right_type = 'FREE' #needed to be able to move the handles
            bezier.bezier_points[i+1].handle_left_type = 'FREE' 
            bezier.bezier_points[i].handle_right = Vector([2*bezier.bezier_points[i].co[j]-bezier.bezier_points[i].handle_left[j] for j in range(len(bezier.bezier_points[i].co))])
            bezier.bezier_points[i+1].handle_left = Vector([bezier.bezier_points[i-1].handle_right[j] + 2*(bezier.bezier_points[i].handle_right[j] - bezier.bezier_points[i].handle_left[j]) for j in range(len(bezier.bezier_points[i].co))])

def frenetify(bezier,calc_res=1000,solid_res=1000):
    sp = FrenetHelper.ToBezierSpline(bezier)
    length = sp.approx_length()
    name = bezier.name
    print("Frenetifying {} (length: {:.2f}).".format(name, length))

    sp = FrenetHelper.ApproximateByC2(sp)
    length = sp.approx_length(minsteps=calc_res)
    FrenetHelper.SolidifyBezierSpline(sp,steps=solid_res) #this seems like a good idea for the number of steps
    print("Smoothed (new length: {:.2f}). Solidified.".format(length))

    #differentiate
    sp_prime = sp.diff()
    sp_pprime = sp_prime.diff()
    
    #make and link new empties
    pos = bpy.data.objects.new(name=(name + "-Pos"), object_data=None)
    tan = bpy.data.objects.new(name=(name + "-Tan"), object_data=None)
    nor = bpy.data.objects.new(name=(name + "-Nor"), object_data=None)
    bin = bpy.data.objects.new(name=(name + "-Bin"), object_data=None)
    bpy.context.scene.objects.link(pos)
    bpy.context.scene.objects.link(tan)
    bpy.context.scene.objects.link(nor)
    bpy.context.scene.objects.link(bin)
    tan.parent = pos
    nor.parent = pos
    bin.parent = pos
    pos.empty_draw_type = 'SPHERE'
    tan.empty_draw_type = 'SPHERE'
    nor.empty_draw_type = 'SPHERE'
    bin.empty_draw_type = 'SPHERE'
    pos.empty_draw_size = 0.02
    tan.empty_draw_size = 0.02
    nor.empty_draw_size = 0.02
    bin.empty_draw_size = 0.02
    
    #make all actions
    action_pos = bpy.data.actions.new(pos.name)
    action_tan = bpy.data.actions.new(tan.name)
    action_nor = bpy.data.actions.new(nor.name)
    action_bin = bpy.data.actions.new(bin.name)

    #make all f-curves
    fcurve_posx = action_pos.fcurves.new("location",index=0)
    fcurve_posy = action_pos.fcurves.new("location",index=1)
    fcurve_posz = action_pos.fcurves.new("location",index=2)
    fcurve_tanx = action_tan.fcurves.new("location",index=0)
    fcurve_tany = action_tan.fcurves.new("location",index=1)
    fcurve_tanz = action_tan.fcurves.new("location",index=2)
    fcurve_norx = action_nor.fcurves.new("location",index=0)
    fcurve_nory = action_nor.fcurves.new("location",index=1)
    fcurve_norz = action_nor.fcurves.new("location",index=2)
    fcurve_binx = action_bin.fcurves.new("location",index=0)
    fcurve_biny = action_bin.fcurves.new("location",index=1)
    fcurve_binz = action_bin.fcurves.new("location",index=2)
    
    fps = bpy.context.scene.render.fps
    frames = floor(length*fps)
    for frame in range(frames+1):
        s = float(frame)/fps
        t = sp.s_to_t(s)
        position   = sp.at_t(t)
        pos_prime  = sp_prime.at_t(t)
        pos_pprime = sp_pprime.at_t(t)
        tangent    = normalize(pos_prime)
        normal     = normalize(cross_product(pos_prime,cross_product(pos_pprime,pos_prime)))
        binormal   = cross_product(tangent,normal)
        
        #insert keyframes
        fcurve_posx.keyframe_points.insert(frame,position[0], options={'FAST'})
        fcurve_posy.keyframe_points.insert(frame,position[1], options={'FAST'})
        fcurve_posz.keyframe_points.insert(frame,position[2], options={'FAST'})
        fcurve_tanx.keyframe_points.insert(frame,tangent[0] , options={'FAST'})
        fcurve_tany.keyframe_points.insert(frame,tangent[1] , options={'FAST'})
        fcurve_tanz.keyframe_points.insert(frame,tangent[2] , options={'FAST'})
        fcurve_norx.keyframe_points.insert(frame,normal[0]  , options={'FAST'})
        fcurve_nory.keyframe_points.insert(frame,normal[1]  , options={'FAST'})
        fcurve_norz.keyframe_points.insert(frame,normal[2]  , options={'FAST'})
        fcurve_binx.keyframe_points.insert(frame,binormal[0], options={'FAST'})
        fcurve_biny.keyframe_points.insert(frame,binormal[1], options={'FAST'})
        fcurve_binz.keyframe_points.insert(frame,binormal[2], options={'FAST'})
    
    #give nice colors
    fcurve_posx.color_mode = 'CUSTOM'
    fcurve_posx.color = (0.6,0.0, 1.0)  
    fcurve_posy.color_mode = 'CUSTOM'
    fcurve_posy.color = (0.6,0.0, 1.0)
    fcurve_posz.color_mode = 'CUSTOM'
    fcurve_posz.color = (0.6,0.0, 1.0)
    fcurve_tanx.color_mode = 'CUSTOM'
    fcurve_tanx.color = (0.6,0.0, 1.0)  
    fcurve_tany.color_mode = 'CUSTOM'
    fcurve_tany.color = (0.6,0.0, 1.0)
    fcurve_tanz.color_mode = 'CUSTOM'
    fcurve_tanz.color = (0.6,0.0, 1.0)
    fcurve_norx.color_mode = 'CUSTOM'
    fcurve_norx.color = (0.6,0.0, 1.0)  
    fcurve_nory.color_mode = 'CUSTOM'
    fcurve_nory.color = (0.6,0.0, 1.0)
    fcurve_norz.color_mode = 'CUSTOM'
    fcurve_norz.color = (0.6,0.0, 1.0)
    fcurve_binx.color_mode = 'CUSTOM'
    fcurve_binx.color = (0.6,0.0, 1.0)  
    fcurve_biny.color_mode = 'CUSTOM'
    fcurve_biny.color = (0.6,0.0, 1.0)
    fcurve_binz.color_mode = 'CUSTOM'
    fcurve_binz.color = (0.6,0.0, 1.0)
    
    #lock the curves
    fcurve_posx.lock = True
    fcurve_posy.lock = True
    fcurve_posz.lock = True
    fcurve_tanx.lock = True
    fcurve_tany.lock = True
    fcurve_tanz.lock = True
    fcurve_norx.lock = True
    fcurve_nory.lock = True
    fcurve_norz.lock = True
    fcurve_binx.lock = True
    fcurve_biny.lock = True
    fcurve_binz.lock = True
    
    # Now bind the action to the target object/datablock.                                                               
    pos.animation_data_create()
    pos.animation_data.action = action_pos
    tan.animation_data_create()
    tan.animation_data.action = action_tan
    nor.animation_data_create()
    nor.animation_data.action = action_nor
    bin.animation_data_create()
    bin.animation_data.action = action_bin



'''
Turn this into a Blender plugin.
'''
class FrenetOperator(bpy.types.Operator):
    '''Calculate Frenet frame of C^2 approximation of active curve'''
    bl_idname = "object.frenet_operator"
    bl_label = "Frenetify Bezier curve"
    
    bl_options = {'REGISTER', 'UNDO'}

    calc_res = bpy.props.IntProperty(
        name="Length calc resolution",
        description="Number of segments to use when approximating length of a curve",
        default=1000,
        min=10,
        soft_min=10,
        max=10000,
        soft_max=10000)
    solid_res = bpy.props.IntProperty(
        name="Solidify resolution",
        description="Number of segments to use when solidifying smoothened curve",
        default=1000,
        min=10,
        soft_min=10,
        max=10000,
        soft_max=10000)

    @classmethod
    def poll(cls, context):
        ob = context.active_object
        if ob is None:
            print("none")
            return False
        if ob.type != "CURVE":
            print("not curve")
            return False
        if len(ob.data.splines)<1:
            print("no splines")
            return False
        if ob.data.splines[0].type != "BEZIER":
            print("not bezier")
            return False
        print(ob.name)
        return True

    def execute(self, context):
        frenetify(context.active_object,calc_res=self.calc_res,solid_res=self.solid_res)
        return {'FINISHED'}

def add_button(self, context):
    self.layout.operator(FrenetOperator.bl_idname, text="Frenetify curve", icon='PLUGIN')

def register():
    bpy.utils.register_class(FrenetOperator)
    bpy.types.VIEW3D_MT_object.append(add_button)

if __name__ == "__main__":
    register()
