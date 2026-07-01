from proveit import Function, Literal,equality_prover
from proveit import x, n, i, a, b, A, B, f, j
from proveit.core_expr_types import x_1_to_n
from proveit.logic import InSet

class Adj(Function):

    _operator_ = Literal(string_format='Adj', theory=__file__)

    def __init__(self, lin_op, *, styles=None):
        '''
        Denote the Hermitan adjoint of a linear operator.
        '''
        Function.__init__(self, Adj._operator_, lin_op,
                          styles=styles)

    def style_options(self):
        from proveit._core_.expression.style_options import StyleOptions
        options = StyleOptions(self)
        options.add_option(
            name = 'notation',
            description = ("Could be 'normal' or 'Dirac' (for quantum notation)"),
            default = 'normal', 
            related_methods = ('with_notation'))
        return options

    def with_notation(self, notation):
        return self.with_styles(notation=notation)


    def latex(self, **kwargs):
        _a = self.operand
        def _is_ket_variable(expr):
            from proveit._core_.expression.label.var import Variable
            if not isinstance(expr, Variable):
                return False
            latex = expr.latex()
            return latex.startswith(r'\lvert') and latex.endswith(r'\rangle')
        
        def _strip_ket_delimiters(latex):
            return latex.replace(r'\lvert', '').replace(r'\rangle', '').strip()


        notation = self.get_style('notation', 'normal')

        # if (notation == 'dirac') and (_is_ket_variable(_a)):

        #     inner = _strip_ket_delimiters(_a.latex())

        #     return r'\langle %s \rvert' % (inner)

        if (notation == 'dirac'):

            if (_is_ket_variable(_a)):
                inner = _strip_ket_delimiters(_a.latex())
                return r'\langle %s \rvert' % (inner) 

            from proveit.physics.quantum import Ket, Bra
            if isinstance(_a, Ket):    
                inner = _a.operands[0].latex()
                return r'\langle %s \rvert' % (inner) 
            
        

        return self.operand.latex(fence=True) + r'^{\dagger}'
    
    ##### newly added
    @equality_prover('distributed', 'distribute')
    def distribution(self,**defaults_config):
        if hasattr(self.operand, 'adjoint_distribution'):
            return self.operand.adjoint_distribution()
        
    


    def string(self, **kwargs):
        _a = self.operand
        from proveit.physics.quantum import Ket, Bra
        def _is_ket_variable(expr):
            from proveit._core_.expression.label.var import Variable
            if not isinstance(expr, Variable):
                return False
            latex = expr.latex()
            return latex.startswith(r'\lvert') and latex.endswith(r'\rangle')
        
        def _strip_ket_delimiters(latex):
            return latex.replace(r'\lvert', '').replace(r'\rangle', '').strip()

        if _is_ket_variable(_a):
            inner = _strip_ket_delimiters(_a.latex())
            # return '<%s|' % (inner)
            return '<%s|' % (inner)
        
        elif isinstance(_a, Ket):    
            inner = _a.operands[0].latex()
            return '<%s|' % (inner)

        return self.operand.string(fence=True) + '*'

    # def string(self, **kwargs):
    #     # replace with unicode dagger when unicode formats are
    #     # implemented
    #     return self.operand.string(fence=True) + '*'

    # def latex(self, **kwargs):
    #     return self.operand.string(fence=True) + r'^{\dagger}'

    def formatted(self, format_type, **kwargs):

        from proveit._core_.expression import maybe_fenced_string
        inner_str = self.operand.formatted(
            format_type,
            fence=True,
            force_fence=True
        )

        if format_type == 'latex':
            formatted_str = inner_str + r'^{\dagger}'
        else:
            formatted_str = inner_str + '^*'

        kwargs['fence'] = (
            kwargs['force_fence']
            if 'force_fence' in kwargs else False
        )

        return maybe_fenced_string(formatted_str, **kwargs)


    @equality_prover('shallow_simplified', 'shallow_simplify')
    def shallow_simplification(self, *, must_evaluate=False,
                               **defaults_config):
        _a = self.operand
        

        from proveit.physics.quantum.HHL import (adjoint_of_ket, adjoint_of_linear_combination_n_terms, 
        adjoint_tensor_upto_n, adjoint_scalar_mult,adjoint_vecsum, adj_of_adj, adj_of_tensor_exp, adj_qmult, adj_scalar)
        from proveit.physics.quantum import Ket, Hspace, Qmult
        from proveit.linear_algebra import VecSum, TensorProd, ScalarMult, TensorExp
        from proveit import ExprTuple, Lambda
        from proveit.numbers import num, Mult, Complex
        from proveit.physics.quantum.HHL.complexity import _ket_uj_domain

        simp = None
        if isinstance(_a,Ket):
            simp = adjoint_of_ket.instantiate({x:_a.operand})
            return simp
        
        if isinstance(_a, Adj):
            simp = adj_of_adj.instantiate({x:_a.operand})
            return simp
            
        if isinstance(_a, VecSum):
            print("in vecsum!")
            print(type(_a))
            _ub = _a.domain.upper_bound
            _lb = _a.domain.lower_bound
            _i = _a.operand.parameter
            simp = adjoint_vecsum.instantiate({a:_lb, b:_ub,i:_i, x:Lambda(_i, _a.instance_expr)})
            return simp

        if isinstance(_a, TensorProd):
            print("in tensorprod!")
            # n = _a.operands.num_entries()
            entries = _a.operands.entries
            num_ent = num(len(entries))
            tensor_terms = ExprTuple(*entries)
            simp = adjoint_tensor_upto_n.instantiate({n:num_ent, x:entries})
            return simp
            
        if isinstance(_a, ScalarMult):
            simp = adjoint_scalar_mult.instantiate({a:_a.scalar,x:_a.scaled})
            return simp
        
        if isinstance(_a, TensorExp):
            simp = adj_of_tensor_exp.instantiate({n:_a.exponent,x:_a.base})
            return simp
        
        if isinstance(_a, Qmult):
            simp = adj_qmult.instantiate({A:_a.operands[0],B:_a.operands[1]})
            return simp
        
        if InSet(_a, Complex).readily_provable():
            simp = adj_scalar.instantiate({x:_a})
            return simp

    


        return Function.shallow_simplification(self, must_evaluate = must_evaluate)


       