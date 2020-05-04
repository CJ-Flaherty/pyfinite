# Copyright Emin Martinian 2002.  See below for license terms.
# Version Control Info: $Id: ffield.py,v 1.5 2007/03/15 02:49:44 emin Exp $

"""
This package contains the FField class designed to perform calculations
in finite fields of characteristic two.  The following docstrings provide
detailed information on various topics:

  FField.__doc__    Describes the methods of the FField class and how
                    to use them.

  FElement.__doc__  Describes the FElement class and how to use it.

  fields_doc        Briefly describes what a finite field is and
                    establishes notation for further documentation.

  design_doc        Discusses the design of the FField class and attempts
                    to justify why certain decisions were made.

  license_doc       Describes the license and lack of warranty for
                    this code.

  testing_doc       Describes some tests to make sure the code is working
                    as well as some of the built in testing routines.

"""
import random, os, os.path, pickle, itertools, copy
import sys
from functools import reduce

gPrimitivePolys = {}
gPrimitivePolysCondensed = {
    1: (1, 0),
    2: (2, 1, 0),
    3: (3, 1, 0),
    4: (4, 1, 0),
    5: (5, 2, 0),
    6: (6, 4, 3, 1, 0),
    7: (7, 1, 0),
    8: (8, 4, 3, 2, 0),
    9: (9, 4, 0),
    10: (10, 6, 5, 3, 2, 1, 0),
    11: (11, 2, 0),
    12: (12, 7, 6, 5, 3, 1, 0),
    13: (13, 4, 3, 1, 0),
    14: (14, 7, 5, 3, 0),
    15: (15, 5, 4, 2, 0),
    16: (16, 5, 3, 2, 0),
    17: (17, 3, 0),
    18: (18, 12, 10, 1, 0),
    19: (19, 5, 2, 1, 0),
    20: (20, 10, 9, 7, 6, 5, 4, 1, 0),
    21: (21, 6, 5, 2, 0),
    22: (22, 12, 11, 10, 9, 8, 6, 5, 0),
    23: (23, 5, 0),
    24: (24, 16, 15, 14, 13, 10, 9, 7, 5, 3, 0),
    25: (25, 8, 6, 2, 0),
    26: (26, 14, 10, 8, 7, 6, 4, 1, 0),
    27: (27, 12, 10, 9, 7, 5, 3, 2, 0),
    28: (28, 13, 7, 6, 5, 2, 0),
    29: (29, 2, 0),
    30: (30, 17, 16, 13, 11, 7, 5, 3, 2, 1, 0),
    31: (31, 3, 0),
    32: (32, 15, 9, 7, 4, 3, 0),
    33: (33, 13, 12, 11, 10, 8, 6, 3, 0),
    34: (34, 16, 15, 12, 11, 8, 7, 6, 5, 4, 2, 1, 0),
    35: (35, 11, 10, 7, 5, 2, 0),
    36: (36, 23, 22, 20, 19, 17, 14, 13, 8, 6, 5, 1, 0),
    37: (37, 5, 4, 3, 2, 1, 0),
    38: (38, 14, 10, 9, 8, 5, 2, 1, 0),
    39: (39, 15, 12, 11, 10, 9, 7, 6, 5, 2, 0),
    40: (40, 23, 21, 18, 16, 15, 13, 12, 8, 5, 3, 1, 0),
    97: (97, 6, 0),
    100: (100, 15, 0)
}

for n in gPrimitivePolysCondensed.keys():
    gPrimitivePolys[n] = [0] * (n + 1)
    unity = 1
    for index in gPrimitivePolysCondensed[n]:
        gPrimitivePolys[n][index] = unity
    gPrimitivePolys[n].reverse()

if sys.version_info[0] >= 3:
    def long(data):
        "Fake the `long` function since not needed after python 2"
        return data

with open('CPolys_dict.txt', 'rb') as handle:
    CPolys_dict = pickle.loads(handle.read())


class FField:
    """
    The FField class implements a finite field calculator.  The
    following functions are provided:
    __init__
    Add 
    Subtract
    Multiply 
    Inverse
    Divide
    FindDegree
    MultiplyWithoutReducing
    ExtendedEuclid
    FullDivision
    ShowCoefficients
    ShowPolynomial
    GetRandomElement
    ConvertListToElement
    TestFullDivision
    TestInverse

    Most of these methods take integers or longs representing field
    elements as arguments and return integers representing the desired
    field elements as output.  See ffield.fields_doc for an explanation
    of the integer representation of field elements.

    Example of how to use the FField class:

>>> import ffield
>>> F = ffield.FField(2,5) # create the field GF(2^5)
>>> a = 7 # field elements are denoted as integers from 0 to 2^5-1
>>> b = 15
>>> F.ShowPolynomial(a) # show the polynomial representation of a
'x^2 + x^1 + 1'
>>> F.ShowPolynomial(b)
'x^3 + x^2 + x^1 + 1'
>>> c = F.Multiply(a,b) # multiply a and b modulo the field generator
>>> c
8
>>> F.ShowPolynomial(c)
'x^3'
>>> F.Multiply(c,F.Inverse(a)) == b # verify multiplication works
1
>>> F.Multiply(c,F.Inverse(b)) == a # verify multiplication works
1
>>> d = F.Divide(c,b) # since c = F.Multiply(a,b), d should give a
>>> d
7

    See documentation on the appropriate method for further details.
    """

    def __init__(self, p, n, gen=0, useLUT=-1):
        """
        This method constructs the field GF(p^n).  It takes 2
        required arguments, a prime p and an integer n, and two optional arguments, gen,
        representing the coefficients of the generator polynomial
        (of degree n) to use and useLUT describing whether to use
        a lookup table.  If no gen argument is provided, the
        Conway Polynomial of degree n is obtained from the table
        gPrimitivePolys.

        If useLUT = 1 then a lookup table is used for
        computing finite field multiplies and divides.
        If useLUT = 0 then no lookup table is used.
        If useLUT = -1 (the default), then the code
        decides when a lookup table should be used.

        Note that you can look at the generator for the field object
        F by looking at F.generator.
        """
        self.n = n
        self.p = p
        self.order = p ** n

        if p == 2:  # Field has characteristic 2, use bitwise operations

            if gen:
                self.generator = gen
            else:
                self.generator = self.ConvertListToElement(gPrimitivePolys[self.n])
            if useLUT == 1 or (useLUT == -1 and self.n < 10):  # use lookup table
                self.zero = 0
                self.unity = 1
                self.root_substitution = self.generator - self.order  # order equiv to poly with 1 at nth degree
                self.element_to_power = {}
                self.power_to_element = {}
                self.AddHelper = self.Char2Add
                self.Add = self.Char2Add
                self.Subtract = self.Char2Add
                self.Inverse = self.LUTInverse
                self.Multiply = self.LUTMultiply
                self.Divide = self.LUTDivide
                self.Char2GenerateDiscreteLogTable()
                #self.Add = self.Char2Add
                #self.Subtract = self.Char2Add  # in fields with char 2, x+y = x-y for all x and y
                #self.Inverse = self.Char2Inverse
                #self.Multiply = self.Char2Multiply
                #self.Divide = self.Char2Divide
            elif self.n < 15:
                self.unity = 1
                self.Add = self.Char2Add
                self.Subtract = self.Char2Add  # in fields with char 2, x+y = x-y for all x and y
                self.Inverse = self.Char2Inverse
                self.Multiply = self.Char2Multiply
                self.Divide = self.Char2Divide
            else:  # Need to use longs for larger fields
                self.unity = long(1)
                self.Inverse = self.Char2InverseForBigField
                self.Multiply = lambda a, b: self.Char2Multiply(long(a), long(b))
                self.Divide = lambda a, b: self.Char2Divide(long(a), long(b))
                self.Add = self.Char2Add
                self.Subtract = self.Char2Add

        elif n == 1:
            self.zero = 0

            self.unity = 1

            self.Add = self.IntegerModularAdd
            self.Multiply = self.IntegerModularMultiply
            self.Divide = self.IntegerModularDivide
            self.Subtract = self.IntegerModularSubtract
            self.Inverse = self.IntegerModularInverse

        else:
            if p != 2:
                self.underlying_field = FField(p, 1)
                self.zero = Polynomial([0], self.underlying_field)
                self.unity = Polynomial([1], self.underlying_field)
                if gen:
                    self.generator = gen
                else:
                    self.generator = Polynomial(CPolys_dict[p][n], self.underlying_field)

                if self.order < 2 ** 15:
                    self.root_substitution = self.GetRootSubstitution()
                    self.element_to_power = [0 for _ in range(self.order)]
                    self.power_to_element = [0 for _ in range(self.order)]
                    self.GenerateDiscreteLogTable()
                    self.AddHelper = self.PolyAdd
                    self.Add = self.PolyAdd  # LUT
                    self.Multiply = self.LUTMultiply
                    self.Divide = self.LUTDivide
                    self.Subtract = self.PolySubtract  # LUT
                    self.Inverse = self.LUTInverse

                else:

                    self.Add = self.PolyAdd
                    self.Multiply = self.PolyMultiply
                    self.Divide = self.PolyDivide
                    self.Subtract = self.PolySubtract
                    self.Inverse = self.PolyInverse

    def LUTAdd(self, a, b):
        """
        Uses Zech's Logarithms to perform addition in finite fields
        via a look up table.

        """
        a_power = self.element_to_power[hash(a)]
        b_power = self.element_to_power[hash(b)]
        return self.power_to_element[a_power + self.GetZechsLog((b_power - a_power) % self.p)]

    def LUTSubtract(self, a, b):
        """
        Uses Zech's Logarithms to perform addition in finite fields
        via a look up table.

        """
        if self.p == 2:
            e = 0
        else:
            e = (self.order - 1) / 2
        a_power = self.element_to_power[hash(a)]
        b_power = self.element_to_power[hash(b)]
        return self.power_to_element[a_power + self.GetZechsLog((e + b_power - a_power) % self.p)]

    def Char2Add(self, x, y):
        """
        Adds two field elements and returns the result.
        """

        return x ^ y

    def Char2Divide(self, f, v):
        """
        Divide(f,v) returns f * v^-1.
        """
        return self.Char2Multiply(f, self.Inverse(v))

    def Char2MultiplyWithoutReducing(self, f, v):
        """
        Multiplies two field elements and does not take the result
        modulo self.generator.  You probably should not use this
        unless you know what you are doing; look at Multiply instead.

        NOTE: If you are using fields larger than GF(2^15), you should
        make sure that f and v are longs not integers.
        """

        result = 0
        mask = self.unity

        for _ in range(self.n + 1):
            if (mask & v):
                result = result ^ f
            f = f << 1
            mask = mask << 1
        return result

    def Char2Multiply(self, f, v):
        """
        Multiplies two field elements (modulo the generator
        self.generator) and returns the result.

        See MultiplyWithoutReducing if you don't want multiplication
        modulo self.generator.
        """
        m = self.Char2MultiplyWithoutReducing(f, v)
        return self.Char2FullDivision(m, self.generator,
                                      self.Char2FindDegree(m), self.n)[1]

    def Char2Inverse(self, f):
        """
        Computes the multiplicative inverse of its argument and
        returns the result.
        """
        return self.Char2ExtendedEuclid(1, f, self.generator,
                                        self.Char2FindDegree(f), self.n)[1]

    def Char2InverseForBigField(self, f):
        """
        Computes the multiplicative inverse of its argument and
        returns the result.
        """
        return self.Char2ExtendedEuclid(self.unity, long(f), self.generator,
                                        self.Char2FindDegree(long(f)), self.n)[1]

    def Char2FindDegree(self, v):
        """
        Find the degree of the polynomial representing the input field
        element v.  This takes O(degree(v)) operations.

        A faster version requiring only O(log(degree(v)))
        could be written using binary search...
        """

        if v:
            result = -1
            while v:
                v = v >> 1
                result = result + 1
            return result
        return 0

    def Char2ExtendedEuclid(self, d, a, b, aDegree, bDegree):
        """
        Takes arguments (d,a,b,aDegree,bDegree) where d = gcd(a,b)
        and returns the result of the extended Euclid algorithm
        on (d,a,b).
        """
        if b == 0:
            return (a, self.unity, 0)
        else:
            (floorADivB, aModB) = self.Char2FullDivision(a, b, aDegree, bDegree)
            (d, x, y) = self.Char2ExtendedEuclid(d, b, aModB, bDegree,
                                                 self.Char2FindDegree(aModB))
            return (d, y, self.Subtract(x, self.Char2Multiply(floorADivB, y)))

    def Char2FullDivision(self, f, v, fDegree, vDegree):
        """
        Takes four arguments, f, v, fDegree, and vDegree where
        fDegree and vDegree are the degrees of the field elements
        f and v represented as a polynomials.
        This method returns the field elements a and b such that

            f(x) = a(x) * v(x) + b(x).

        That is, a is the divisor and b is the remainder, or in
        other words a is like floor(f/v) and b is like f modulo v.
        """

        result = 0
        i = fDegree
        mask = self.unity << i
        while i >= vDegree:
            if mask & f:
                result = result ^ (self.unity << (i - vDegree))
                f = self.Subtract(f, v << (i - vDegree))
            i = i - 1
            mask = mask >> self.unity
        return (result, f)

    def ConvertListToElement(self, l):
        """
        This method takes as input a binary list (e.g. [1, 0, 1, 1])
        and converts it to a decimal representation of a field element.
        For example, [1, 0, 1, 1] is mapped to 8 | 2 | 1 = 11.

        Note if the input list is of degree >= to the degree of the
        generator for the field, then you will have to call take the
        result modulo the generator to get a proper element in the
        field.
        """

        temp = map(lambda a, b: a << b, l, range(len(l) - 1, -1, -1))
        return reduce(lambda a, b: a | b, temp)

    def LUTInverse(self, a):
        """
        Uses a look up table to compute an element's inverse

        Say the field's multiplicative group has order q and element = generator^e
        Then e^-1 = generator^{q-e}
        """
        element_power = self.element_to_power[hash(a)]
        return self.power_to_element[self.order - element_power - 1]

    def LUTMultiply(self, a, b):
        """
        Uses discrete logarithms to perform multiplication with a look up table
        """
        if a == self.zero or b == self.zero:
            return self.zero
        a_power = self.element_to_power[hash(a)]
        b_power = self.element_to_power[hash(b)]
        return self.power_to_element[(a_power + b_power) % (self.order - 1)]

    def LUTDivide(self, a, b):
        """
        Uses discrete logariths to perform division with a look up table.
        """
        if a == self.zero:
            return self.zero
        a_power = self.element_to_power[hash(a)]
        b_power = self.element_to_power[hash(b)]
        return self.power_to_element[(a_power - b_power) % (self.order - 1)]

    def GetRootSubstitution(self):
        """
        say we have generating polynomial g(x) = x^3 +x +1
        Since we assume g(x) has a root in our field, we have
        x^3 =0 -(x +1)
        That is, when generating our field, any cubic term can be replaced with -x +-1
        """
        temp = self.zero - self.generator
        sub_coeffs = temp.coeffs
        sub_coeffs[self.n] = 0
        return Polynomial(sub_coeffs, self.underlying_field)

    def Char2GenerateDiscreteLogTable(self):
        """
        Generates a discrete log table in fields of characteristic 2.
        Uses same logic as GenerateDiscreteLogTable, but with bitwise operators
        """
        lutName = 'ffield.lut.' + repr(self.order) + str(self.generator)
        if os.path.exists(lutName):
            self.power_to_element, self.element_to_power = pickle.load( open( lutName, "rb" ) )
        else:
            L = [0 for x in range(self.order)]
            L[0] = copy.copy(self.unity)
            self.element_to_power[self.unity] = 0
            self.power_to_element[0] = copy.copy(self.unity)
            for i in range(1, self.order - 1):
                element = L[i - 1] << 1
                if element >= self.order:
                    element -= self.order
                    element = self.Add(element, self.root_substitution)
                L[i] = element
                self.element_to_power[element] = i
                self.power_to_element[i] = element
            pickle.dump(self.power_to_element, self.element_to_power, fd)

    def GenerateDiscreteLogTable(self):
        """
        Generates a Discrete Logarithm table by repeatedly exponentiating the generator.
        When the result of this exonentiation has degree equal to the degree of the generating 
        polynomial, we add the root substitution and set the nth degree term of the polynomial equal
        to zero. This is equivalent to taking the remainder modulo the generator.
        """

        lutName = 'ffield.lut.' + repr(self.order) + str(self.generator)
        if (os.path.exists(lutName)):
            self.power_to_element, self.element_to_power = pickle.load( open(lutName, "rb" ) )
            
        else:
            x = Polynomial([0, 1], self.underlying_field)  # equiv to the polynomial x
            L = [0 for x in range(self.order)]
            L[0] = copy.copy(self.unity)
            self.element_to_power[hash(self.unity)] = 0
            self.power_to_element[0] = copy.copy(self.unity)
            for i in range(1, self.order - 1):
                poly = L[i - 1] * x
                if poly.degree == self.n:
                    for _ in range(poly.coeffs[self.n]):
                        poly += self.root_substitution
                    reduced_coeffs = poly.coeffs
                    reduced_coeffs[self.n] = 0
                    poly = Polynomial(reduced_coeffs, self.underlying_field)
                L[i] = poly
                self.element_to_power[hash(poly)] = i
                self.power_to_element[i] = poly
            pickle.dump(self.power_to_element, self.element_to_power, open(lutName, "wb" ))

    def PolyAdd(self, a, b):
        """
        Adds 2 polynomials
        """
        return a + b

    def PolySubtract(self, a, b):
        """
        Subtracts 2 polynomials
        """
        return a - b

    def PolyMultiply(self, a, b):
        """
        Multiplies 2 polynomials according to the field
        """
        return (a * b) % self.generator

    def PolyDivide(self, a, b):
        """
        Divides 2 polynomials according to the field
        """
        b = self.Inverse(b)
        return self.PolyMultiply(a, b)

    def PolyInverse(self, a):
        """
        Finds the multiplicative inverse of a in the field
        """
        return self.ExtendedEuclid(a, self.generator)[0] % self.generator

    def IntegerModularAdd(self, a, b):
        """
        Adds 2 integers in Z_p
        used when n == 1
        """
        return (a + b) % self.p

    def IntegerModularSubtract(self, a, b):
        """
        Subtracts 2 integers in Z_p
        used when n == 1
        """ 

        return (a - b) % self.p

    def IntegerModularMultiply(self, a, b):
        """
        Multiplies 2 integers in Z_p
        used when n == 1
        """
        return (a * b) % self.p

    def IntegerModularDivide(self, a, b):
        """
        Divides 2 integers in Z_p
        used when n == 1
        """
        b = self.IntegerModularInverse(b)
        return (a * b) % self.p

    def IntegerModularInverse(self, a):
        """
        Finds a^-1 in Z_p
        used when n == 1

        say a = generator^x
        Then a^{(p-2)} * a^x = a^{p-1}

        and since Z_p's multiplicative group has order p-1,
        a^{p-2} = a^-1
        """
        return a ** (self.p - 2) % self.p

    def ExtendedEuclid(self, a, b):
        """Performs the extended euclidean algorithm on a, b
        returning old_s, old_t, old_r such that
        old_s*a +old_t*b = old_r = gcd(a,b)
        """ 
        s = copy.copy(self.zero)
        old_s = copy.copy(self.unity)
        t = copy.copy(self.unity)
        old_t = copy.copy(self.zero)
        r = b
        old_r = a
        while r != self.zero:
            quotient = old_r // r
            old_r, r = r, old_r - (quotient * r)
            old_s, s = s, old_s - (quotient * s)
            old_t, t = t, old_t - (quotient * t)
        return [old_s, old_t, old_r]

    def TestChar2FullDivision(self):
        """
        Test the FullDivision function by generating random polynomials
        a(x) and b(x) and checking whether (c,d) == FullDivision(a,b)
        satsifies b*c + d == a
        """
        a = self.GetRandomElement(nonZero=1)
        b = self.GetRandomElement(nonZero=1)
        aDegree = self.FindDegree(a)
        bDegree = self.FindDegree(b)
        (c, d) = self.Char2FullDivision(a, b, aDegree, bDegree)
        recon = self.Add(d, self.Multiply(c, b))
        assert (recon == a), ('TestFullDivision failed: a='
                              + repr(a) + ', b=' + repr(b) + ', c='
                              + repr(c) + ', d=' + repr(d) + ', recon=', recon)

    def TestChar2Inverse(self):
        """
        This function tests the Inverse function by generating
        a random non-zero polynomials a(x) and checking if
        a * Inverse(a) == 1.
        """
        a = self.GetRandomElement(nonZero=1)
        aInv = self.Char2Inverse(a)
        prod = self.Multiply(a, aInv)
        assert 1 == prod, ('TestChar2Inverse failed:' + 'a=' + repr(a) + ', aInv='
                           + repr(aInv) + ', prod=' + repr(prod),
                           'gen=' + repr(self.generator))

    def GetRandomElement(self, nonZero=0, maxDegree=None):
        """
        Return an element from the field chosen uniformly at random
        or, if the optional argument nonZero is true, chosen uniformly
        at random from the non-zero elements, or, if the optional argument
        maxDegree is provided, ensure that the result has degree less
        than maxDegree.
        """

        if (None == maxDegree):
            maxDegree = self.n
        if (maxDegree <= 1 and nonZero):
            return 1
        if (maxDegree < 31):
            return random.randint(nonZero != 0, (1 << maxDegree) - 1)
        else:
            result = 0
            for i in range(0, maxDegree):
                result = result ^ (random.randint(0, 1) << long(i))
            if (nonZero and result == 0):
                return self.GetRandomElement(1)
            else:
                return result

    def FindDegree(self, v):
        """
        Find the degree of the polynomial representing the input field
        element v.  This takes O(degree(v)) operations.

        A faster version requiring only O(log(degree(v)))
        could be written using binary search...
        """

        if v:
            result = -1
            while v:
                v = v >> 1
                result = result + 1
            return result
        return 0

    def ShowCoefficients(self, f):
        """
        Show coefficients of input field element represented as a
        polynomial in decreasing order.
        """

        fDegree = self.n

        result = []
        for i in range(fDegree, -1, -1):
            if ((self.unity << i) & f):
                result.append(1)
            else:
                result.append(0)

        return result

    def ShowPolynomial(self, f):
        """
        Show input field element represented as a polynomial.
        """

        fDegree = self.FindDegree(f)
        result = ''

        if f == 0:
            return '0'

        for i in range(fDegree, 0, -1):
            if (1 << i) & f:
                result = result + (' x^' + repr(i))
        if 1 & f:
            result = result + ' ' + repr(1)
        return result.strip().replace(' ', ' + ')

    def GetZechsLog(self, argument):
        """
        argument is an integer
        """
        element = self.AddHelper(self.unity, self.power_to_element[argument])
        return self.element_to_power[element]




class Polynomial:
    """
    Implements polynomials using a list to store coefficients.
    Accepts a field
    Addition
    Subtraction
    Multiplication
    Division

    """

    def __init__(self, coeffs, field):
        """
        initiates a polynomial object over field 
        with coefficients from coeffs
        strips 0's from end of coefficient list on init.
        """
        for i in reversed(coeffs[1:]):
            if not i:
                del coeffs[-1]
            else:
                break
        self.coeffs = coeffs
        self.degree = len(self.coeffs) - 1
        self.field = field

    def __str__(self):
        """
        from:
        https://stackoverflow.com/questions/34843514/printing-a-polynomial-in-python
        Łukasz Rogalski
        """
        chunks = []
        for coeff, power in zip(self.coeffs, range(len(self.coeffs))):
            if coeff == 0:
                continue
            chunks.append(self.format_coeff(coeff))
            chunks.append(self.format_power(power))
        chunks[0] = chunks[0].lstrip("+")
        return ''.join(chunks)

    @staticmethod
    def format_coeff(coeff):
        return str(coeff) if coeff < 0 else "+{0}".format(coeff)

    @staticmethod
    def format_power(power):
        return 'x^{0}'.format(power) if power != 0 else ''

    def __eq__(self, other):
        """
        2 polynomials are equal iff they have the same coeff list
        """
        if not isinstance(other, Polynomial):
            return False

        for x, y in itertools.zip_longest(self.coeffs, other.coeffs, fillvalue=0):
            if x != y:
                return False

        return True

    def __add__(self, other):
        """
        adds polynomials according to operations in the underlying field
        """
        newCoeffs = [self.field.Add(x, y) for x, y in itertools.zip_longest(self.coeffs, other.coeffs, fillvalue=0)]

        return Polynomial(newCoeffs, self.field)

    def __sub__(self, other):
        """
        subtracts polynomials according to operations in underlying field
        """
        newCoeffs = [self.field.Subtract(x, y) for x, y in
                     itertools.zip_longest(self.coeffs, other.coeffs, fillvalue=0)]

        return Polynomial(newCoeffs, self.field)

    def __mul__(self, other):
        """
        multiplies polynomials according to operations in underlying field

        
        """
        newCoeffs = [0 for _ in range(max(self.degree + 1, other.degree + 1) * 2)]
        for deg_1, coeff_1 in enumerate(self.coeffs):
            for deg_2, coeff_2 in enumerate(other.coeffs):
                newCoeffs[deg_1 + deg_2] = self.field.Add(newCoeffs[deg_1 + deg_2], #deg_1 + deg_2 according to normal addition.
                                                          self.field.Multiply(coeff_1, coeff_2)) 
        return Polynomial(newCoeffs, self.field)

    def __truediv__(self, other):
        """
        Divides 2 polynomials, using underlying field operations on coefficients
        """
        result = [0 for _ in range((self.degree - other.degree) + 1)]
        f = Polynomial(self.coeffs, self.field)
        v = Polynomial(other.coeffs, other.field)

        while f.degree >= v.degree and (f != Polynomial([0], self.field) and v != Polynomial([0], self.field)):
            shift = f.degree - v.degree
            shift_Lst = [0 for _ in range(shift + 1)]
            shift_Lst[shift] = 1
            shift_poly = Polynomial(shift_Lst, self.field)
            v = v * shift_poly
            result[shift] = self.field.Divide(f.coeffs[f.degree], v.coeffs[v.degree])
            v = v * Polynomial([result[shift]], self.field)
            f = f - v
            v = Polynomial(other.coeffs, other.field)

        return (Polynomial(result, self.field), f)

    def __mod__(self, other):
        """
        remainder of self divided by other
        self%other
        """
        return self.__truediv__(other)[1]

    def __floordiv__(self, other):
        """
        self//other
        """
        return self.__truediv__(other)[0]

    def __hash__(self):
        """
        polynomials are hashed by reversing their coeff lists
        and considering that a number base p
        """
        s = "".join(str(x) for x in self.coeffs)

        return int(s[::-1], self.field.p)


class FElement:
    """
    This class provides field elements which overload the
    +,-,*,%,//,/ operators to be the appropriate field operation.
    Note that before creating FElement objects you must first
    create an FField object.  For example,

>>> import ffield
>>> F = ffield.FField(2,5)
>>> e1 = ffield.FElement(F,7)
>>> e1
x^2 + x^1 + 1
>>> e2 = ffield.FElement(F,19)
>>> e2
x^4 + x^1 + 1
>>> e3 = e1 + e2
>>> e3
x^4 + x^2
>>> e4 = e3 / e2
>>> e4
x^4 + x^3
>>> e4 * e2 == (e3)
1

    """

    def __init__(self, field, e):
        """
        The constructor takes two arguments, field, and e where
        field is an FField object and e is an integer representing
        an element in FField.

        The result is a new FElement instance.
        """
        self.f = e
        self.field = field

    def __add__(self, other):
        assert self.field == other.field
        return FElement(self.field, self.field.Add(self.f, other.f))

    def __mul__(self, other):
        assert self.field == other.field
        return FElement(self.field, self.field.Multiply(self.f, other.f))

    def __mod__(self, o):
        assert self.field == o.field
        return FElement(self.field,
                        self.field.FullDivision(self.f, o.f,
                                                self.field.FindDegree(self.f),
                                                self.field.FindDegree(o.f))[1])

    def __floordiv__(self, o):
        assert self.field == o.field
        return FElement(self.field,
                        self.field.FullDivision(self.f, o.f,
                                                self.field.FindDegree(self.f),
                                                self.field.FindDegree(o.f))[0])

    def __truediv__(self, other):
        assert self.field == other.field
        return FElement(self.field, self.field.Divide(self.f, other.f))

    def __div__(self, *args, **kwargs):
        "syntatic sugar for calling self.__truediv__(*args, **kwargs)"
        return self.__truediv__(*args, **kwargs)

    def __str__(self):
        return self.field.ShowPolynomial(self.f)

    def __repr__(self):
        return self.__str__()

    def __eq__(self, other):
        assert self.field == other.field
        return self.f == other.f


def FullTest(testsPerField=10, sizeList=None):
    """
    This function runs TestInverse and TestFullDivision for testsPerField
    random field elements for each field size in sizeList.  For example,
    if sizeList = (1,5,7), then thests are run on GF(2), GF(2^5), and
    GF(2^7).  If sizeList == None (which is the default), then every
    field is tested.
    """

    if (None == sizeList):
        sizeList = gPrimitivePolys.keys()
    for i in list(sizeList)[1::]:
        F = FField(2, i)
        for _ in range(testsPerField):
            F.TestChar2Inverse()
            F.TestChar2FullDivision()


fields_doc = """
Roughly speaking a finite field is a finite collection of elements
where most of the familiar rules of math work.  Specifically, you
can add, subtract, multiply, and divide elements of a field and
continue to get elements in the field.  This is useful because
computers usually store and send information in fixed size chunks.
Thus many useful algorithms can be described as elementary operations
(e.g. addition, subtract, multiplication, and division) of these chunks.

Currently this package only deals with fields of characteristic 2.  That
is all fields we consider have exactly 2^p elements for some integer p.
We denote such fields as GF(2^p) and work with the elements represented
as p-1 degree polynomials in the indeterminate x.  That is an element of
the field GF(2^p) looks something like

     f(x) = c_{p-1} x^{p-1} + c_{p-2} x^{p-2} + ... + c_0

where the coefficients c_i are in binary.

Addition is performed by simply adding coefficients of degree i
modulo 2.  For example, if we have two field elements f and v
represented as f(x) = x^2 + 1 and v(x) = x + 1 then s = f + v
is given by (x^2 + 1) + (x + 1) = x^2 + x.  Multiplication is
performed modulo a p degree generator polynomial g(x).
For example, if f and v are as in the above example, then s = s * v
is given by (x^2 + 1) + (x + 1) mod g(x).  Subtraction turns out
to be the same as addition for fields of characteristic 2.  Division
is defined as f / v = f * v^-1 where v^-1 is the multiplicative
inverse of v.  Multiplicative inverses in groups and fields
can be calculated using the extended Euclid algorithm.

Roughly speaking the intuition for why multiplication is
performed modulo g(x), is because we want to make sure s * v
returns an element in the field.  Elements of the field are
polynomials of degree p-1, but regular multiplication could
yield terms of degree greater than p-1.  Therefore we need a
rule for 'reducing' terms of degree p or greater back down
to terms of degree at most p-1.  The 'reduction rule' is
taking things modulo g(x).

For another way to think of
taking things modulo g(x) as a 'reduction rule', imagine
g(x) = x^7 + x + 1 and we want to take some polynomial,
f(x) = x^8 + x^3 + x, modulo g(x).  We can think of g(x)
as telling us that we can replace every occurence of
x^7 with x + 1.  Thus f(x) becomes x * x^7 + x^3 + x which
becomes x * (x + 1) + x^3 + x = x^3 + x^2 .  Essentially, taking
polynomials mod x^7 by replacing all x^7 terms with x + 1 will
force down the degree of f(x) until it is below 7 (the leading power
of g(x).  See a book on abstract algebra for more details.
"""

design_doc = """
The FField class implements a finite field calculator for fields of
characteristic two.  This uses a representation of field elements
as integers and has various methods to calculate the result of
adding, subtracting, multiplying, dividing, etc. field elements
represented AS INTEGERS OR LONGS.

The FElement class provides objects which act like a new kind of
numeric type (i.e. they overload the +,-,*,%,//,/ operators, and
print themselves as polynomials instead of integers).

Use the FField class for efficient storage and calculation.
Use the FElement class if you want to play around with finite
field math the way you would in something like Matlab or
Mathematica.

--------------------------------------------------------------------
                           WHY PYTHON?

You may wonder why a finite field calculator written in Python would
be useful considering all the C/C++/Java code already written to do
the same thing (and probably faster too).  The goals of this project
are as follows, please keep them in mind if you make changes:

o  Provide an easy to understand implementation of field operations.
   Python lends itself well to comments and documentation.  Hence,
   we hope that in addition to being useful by itself, this project
   will make it easier for people to implement finite field
   computations in other languages.  If you've ever looked at some
   of the highly optimized finite field code written in C, you will
   understand the need for a clear reference implementation of such
   operations.

o  Provide easy access to a finite field calculator.
   Since you can just start up the Python interpreter and do
   computations, a finite field calculator in Python lets you try
   things out, check your work for other algorithms, etc.
   Furthermore since a wealth of numerical packages exist for python,
   you can easily write simulations or algorithms which draw upon
   such routines with finite fields.

o  Provide a platform independent framework for coding in Python.
   Many useful error control codes can be implemented based on
   finite fields.  Some examples include error/erasure correction,
   cyclic redundancy checks (CRCs), and secret sharing.  Since
   Python has a number of other useful Internet features being able
   to implement these kinds of codes makes Python a better framework
   for network programming.

o  Leverages Python arbitrary precision code for large fields.
   If you want to do computations over very large fields, for example
   GF(2^p) with p > 31 you have to write lots of ugly bit field
   code in most languages.  Since Python has built in support for
   arbitrary precision integers, you can make this code work for
   arbitrary field sizes provided you operate on longs instead of
   ints.  In python 3 this is automatic, but in python2 you need
   to give as input numbers like 0L, 1L, 1L << 55, etc. to force
   using longs.

--------------------------------------------------------------------
                            BASIC DESIGN


The basic idea is to index entries in the finite field of interest
using integers and design the class methods to work properly on this
representation.  Using integers is efficient since integers are easy
to store and manipulate and allows us to handle arbitrary field sizes
without changing the code if we instead switch to using longs.

Specifically, an integer represents a bit string

  c = c_{p-1} c_{p-2} ... c_0.

which we interpret as the coefficients of a polynomial representing a
field element

  f(x) = c_{p-1} x^{p-1} + c_{p-2} x^{p-2} + ... + c_0.

--------------------------------------------------------------------
                             FUTURE
In the future, support for fields of other
characteristic may be added (if people want them).  Since computers
have built in parallelized operations for fields of characteristic
two (i.e. bitwise and, or, xor, etc.), this implementation uses
such operations to make most of the computations efficient.

"""

license_doc = """
  This code was originally written by Emin Martinian (emin@allegro.mit.edu).
  You may copy, modify, redistribute in source or binary form as long
  as credit is given to the original author.  Specifically, please
  include some kind of comment or docstring saying that Emin Martinian
  was one of the original authors.  Also, if you publish anything based
  on this work, it would be nice to cite the original author and any
  other contributers.

  There is NO WARRANTY for this software just as there is no warranty
  for GNU software (although this is not GNU software).  Specifically
  we adopt the same policy towards warranties as the GNU project:

  BECAUSE THE PROGRAM IS LICENSED FREE OF CHARGE, THERE IS NO WARRANTY
FOR THE PROGRAM, TO THE EXTENT PERMITTED BY APPLICABLE LAW.  EXCEPT WHEN
OTHERWISE STATED IN WRITING THE COPYRIGHT HOLDERS AND/OR OTHER PARTIES
PROVIDE THE PROGRAM 'AS IS' WITHOUT WARRANTY OF ANY KIND, EITHER EXPRESSED
OR IMPLIED, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF
MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE.  THE ENTIRE RISK AS
TO THE QUALITY AND PERFORMANCE OF THE PROGRAM IS WITH YOU.  SHOULD THE
PROGRAM PROVE DEFECTIVE, YOU ASSUME THE COST OF ALL NECESSARY SERVICING,
REPAIR OR CORRECTION.

  IN NO EVENT UNLESS REQUIRED BY APPLICABLE LAW OR AGREED TO IN WRITING
WILL ANY COPYRIGHT HOLDER, OR ANY OTHER PARTY WHO MAY MODIFY AND/OR
REDISTRIBUTE THE PROGRAM AS PERMITTED ABOVE, BE LIABLE TO YOU FOR DAMAGES,
INCLUDING ANY GENERAL, SPECIAL, INCIDENTAL OR CONSEQUENTIAL DAMAGES ARISING
OUT OF THE USE OR INABILITY TO USE THE PROGRAM (INCLUDING BUT NOT LIMITED
TO LOSS OF DATA OR DATA BEING RENDERED INACCURATE OR LOSSES SUSTAINED BY
YOU OR THIRD PARTIES OR A FAILURE OF THE PROGRAM TO OPERATE WITH ANY OTHER
PROGRAMS), EVEN IF SUCH HOLDER OR OTHER PARTY HAS BEEN ADVISED OF THE
POSSIBILITY OF SUCH DAMAGES.
"""

testing_doc = """
The FField class has a number of built in testing functions such as
TestFullDivision, TestInverse.  The simplest thing to
do is to call the FullTest method.

>>> import ffield
>>> ffield.FullTest(sizeList=None,testsPerField=100)

# To decrease the testing time you can either decrease the testsPerField
# or you can only test the field sizes you care about by doing something
# like sizeList = [2,7,20] in the ffield.FullTest command above.

If any problems occur, assertion errors are raised.  Otherwise
nothing is returned.  Note that you can also use the doctest
package to test all the python examples in the documentation
by typing 'python ffield.py' or 'python -v ffield.py' at the
command line.
"""

# The following code is used to make the doctest package
# check examples in docstrings.


__test__ = {
    'testing_doc': testing_doc
}


def _test():
    import doctest, ffield
    return doctest.testmod(ffield)


if __name__ == "__main__":
    print('Starting automated tests (this may take a while)')
    _test()
    print('Tests finished.')
