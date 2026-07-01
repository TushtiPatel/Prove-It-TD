from proveit import Operation, Literal, relation_prover, x
from proveit import maybe_fenced_string, maybe_fenced_latex

from proveit.logic import InSet

class Conjugate(Operation):
    '''
    The complex conjugate of a + i b for real numbers a and b is
    equal to a - i b.
    '''

    _operator_ = Literal(string_format='conj', theory=__file__)

    def __init__(self, num, *, styles=None):
        '''
        Create an expression for the complex conjugate of the given
        number.
        '''
        Operation.__init__(self, Conjugate._operator_, num,
                           styles=styles)

    def string(self, **kwargs):
        return maybe_fenced_string(
            self.operand.string(
                fence=True) + '*',
            **kwargs)

    def latex(self, **kwargs):
        return maybe_fenced_latex(
            self.operand.latex(
                fence=True) + "^*",
            **kwargs)
    
    def readily_provable_number_set(self):
        '''
        Return the most restrictive number set we can readily
        prove contains the evaluation of this number operation.
        '''
        from proveit.numbers import readily_provable_number_set
        from proveit.numbers import (
            ZeroSet, Integer, IntegerNonZero, NaturalPos, Natural,
            Rational, RationalNonZero, RationalPos,
            RationalNonNeg, Real, RealNonNeg, RealPos, RealNonZero,
            ComplexNonZero, Complex)
        operand_ns = readily_provable_number_set(self.operand,
                                                 default=Complex)
        if operand_ns is None: return None
        if Real.readily_includes(operand_ns):
            return Real
        return Complex
        

    @relation_prover
    def deduce_in_number_set(self, number_set, **defaults_config):
        '''
        Given a number set number_set (such as Integer, Real, etc),
        attempt to prove that the given expression is in that number
        set using the appropriate closure theorem.
        '''
        import proveit.numbers.number_sets.complex_numbers as complex_pkg
        from proveit.numbers import (
            ZeroSet, Natural, NaturalPos, Integer, IntegerNonZero,
            Rational, RationalNonZero, RationalPos, RationalNonNeg,
            Real, RealNonNeg, RealPos, RealNonZero, ComplexNonZero)

        thm = None
        if number_set in (Real,):
            thm = complex_pkg.conjugate_real_closure            
        else:
            thm = complex_pkg.conjugate_complex_closure

        if thm is not None:
            in_set = thm.instantiate({x: self.operand})
            if in_set.domain == number_set:
                # Exactly the domain we were looking for.
                return in_set
            # We must have proven we were in a subset of the
            # one we were looking for.
            return InSet(self, number_set).prove()

        # # To be thorough and a little more general, we check if the
        # # specified number_set is already proven to *contain* one of
        # # the number sets we have theorems for -- for example,
        # #     Y=Complex contain X=Real, and
        # #     Y=(-1, inf) contains X=RealPos,
        # # but we don't have specific thms for those supersets Y.
        # # If so, use the appropiate thm to determine that self is in X,
        # # then prove that self must also be in Y since Y contains X.
        # if SubsetEq(Real, number_set).readily_provable():
        #     abs_pkg.abs_complex_closure.instantiate({a: self.operand})
        #     return InSet(self, number_set).prove()
        # if SubsetEq(RealPos, number_set).readily_provable():
        #     abs_pkg.abs_nonzero_closure.instantiate({a: self.operand})
        #     return InSet(self, number_set).prove()
        # if SubsetEq(RealNonNeg, number_set).readily_provable():
        #     abs_pkg.abs_complex_closure_non_neg_real.instantiate({a: self.operand})
        #     return InSet(self, number_set).prove()

        # otherwise, we just don't have the right thm to make it work
        raise NotImplementedError(
            "'Abs.deduce_in_number_set()' not implemented for "
            "the %s set" % str(number_set))