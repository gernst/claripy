from claripy import BackendError
from claripy.backends import BackendSMTLibBase
from claripy.smtlib_utils import SMTParser
from claripy.utils import OrderedSet
from six.moves import cStringIO

from pysmt.smtlib.parser import Tokenizer
from pysmt.shortcuts import And, NotEquals

class AbstractSMTLibSolverProxy(object):
    def write(self, smt):
        raise NotImplementedError

    def read(self, n):
        raise NotImplementedError

    def setup(self):
        pass

    def reset(self):
        self.write('(reset)\n')

    def readuntil(self, s):
        buf = ''
        while s not in buf:
            buf += self.read(1)
        return buf

    def readline(self):
        return self.readuntil('\n')

    def writeline(self, l):
        return self.write(l + '\n')

    def read_sat(self):
        return self.readline().strip()

    def read_model(self):
        read_model = self.readuntil('\n)\n').strip()
        return read_model

class PopenSolverProxy(AbstractSMTLibSolverProxy):
    def __init__(self, p):
        super(PopenSolverProxy, self).__init__()
        self.p = p
        self.constraints = []

    def read(self, n):
        return self.p.stdout.read(n)

    def write(self, smt):
        self.p.stdin.write(smt)
        self.p.stdin.flush()

    def add_constraints(self, csts, track=False):
        self.constraints.extend(csts)


class SMTLibSolverBackend(BackendSMTLibBase):
    def __init__(self, *args, **kwargs):
        kwargs['solver_required'] = True
        super(SMTLibSolverBackend, self).__init__(*args, **kwargs)

    def solver(self, timeout=None): #pylint:disable=no-self-use,unused-argument
        """
        This function should return an instance of whatever object handles
        solving for this backend. For example, in Z3, this would be z3.Solver().
        """
        raise NotImplementedError

    def _get_primitive_for_expr(self, model, e):
        substituted = e.substitute(model).simplify()
        if not substituted.is_constant():
            raise BackendError(
                "CVC4 backend currently only supports requests for symbols directly! This is a weird one that doesn't "
                "turn constant after substitution??")

        return substituted.constant_value()

    def _simplify(self, e):
        return e

    def _is_false(self, e, extra_constraints=(), solver=None, model_callback=None):
        if e.is_constant() and e.constant_value() is False:
            return True
        return False

    def _is_true(self, e, extra_constraints=(), solver=None, model_callback=None):
        if e.is_constant() and e.constant_value() is True:
            return True
        return False

    def _batch_eval(self, exprs, n, extra_constraints=(), solver=None, model_callback=None):
        return [self._eval(e, n, extra_constraints=extra_constraints, solver=solver, model_callback=model_callback) for e in exprs]

    def _add(self, s, c, track=False):
        s.add_constraints(c, track=track)

    def _satisfiable(self, extra_constraints=(), solver=None, model_callback=None):
        smt_script = self._get_satisfiability_smt_script(tuple(extra_constraints) + tuple(solver.constraints))
        solver.reset()
        solver.write(smt_script)
        sat = solver.read_sat()
        if sat not in {'sat', 'unsat'}:
            import ipdb; ipdb.set_trace()
            raise ValueError("Solver error, don't understand (check-sat) response: {}".format(repr(sat)))
        return sat == 'sat'

    def _get_model(self, extra_constraints=(), solver=None):
        smt_script = self._get_full_model_smt_script(tuple(extra_constraints) + tuple(solver.constraints))
        solver.reset()
        solver.write(smt_script)
        sat = solver.read_sat()
        if sat == 'sat':
            model_string = solver.read_model()
            tokens = Tokenizer(cStringIO(model_string), interactive=True)
            ass_list = SMTParser(tokens).consume_assignment_list()
            return sat, {s: val for s, val in ass_list}, ass_list
        else:
            error = solver.readline()

        return sat, error, None

    def _eval(self, expr, n, extra_constraints=(), solver=None, model_callback=None):
        e_c = list(extra_constraints)

        if expr.is_constant():
            return [expr.constant_value()]

        results = OrderedSet()
        while len(results) < n:
            sat, model, ass_list = self._get_model(extra_constraints=e_c, solver=solver)
            if sat != 'sat':
                break

            val = self._get_primitive_for_expr(model, expr)
            if val in results:
                raise ValueError("Solver error, solver returned the same value twice incorrectly!")

            results.add(val)
            e_c.append(NotEquals(expr, val))

        return list(results)

from cvc4_popen import SolverBackendCVC4
from z3_popen import SolverBackendZ3
from abc_popen import SolverBackendABC