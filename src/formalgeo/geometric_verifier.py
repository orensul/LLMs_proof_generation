from z3 import *
import re
from dataclasses import dataclass
from typing import Dict, List, Optional, Set, Tuple
from enum import Enum
from typing import Tuple, Optional
from fractions import Fraction
import logging

CONSTRUCTION_CDL = 'CONSTRUCTION_CDL'
TEXT_CDL = 'TEXT_CDL'
GOAL_CDL = 'GOAL_CDL'
CONSTRUCTION_CDL_EXTENDED = 'CONSTRUCTION_CDL_EXTENDED'
THEOREM_SEQUENCE = 'THEOREM_SEQUENCE'
ANSWER = 'ANSWER'
VERIFICATION_FAILED = "verification failed.\n\n"
PLEASE_FIX_PROOF = "\nPlease fix the proof."

# Goal description constants
GOAL_ANGLE = "- Goal: measure of angle {0}\n"
GOAL_LENGTH = "- Goal: length of line {0}\n"
GOAL_ARC_MEASURE = "- Goal: measure of arc {0}\n"
GOAL_RADIUS = "- Goal: radius of circle {0}\n"
GOAL_ARC_LENGTH = "- Goal: length of arc {0}\n"
GOAL_COSINE = "- Goal: cosine of angle {0}\n"
GOAL_SINE = "- Goal: sine of angle {0}\n"
GOAL_SUM = "- Goal: sum of lines {0} + {1}\n"
GOAL_RADIUS = "- Goal: radius of circle {0}\n"
GOAL_RATIO = "- Goal: ratio of lines {0} / {1}\n"
GOAL_PERIMETER = "- Goal: perimeter of triangle {0}\n"
GOAL_QUAD_AREA = "- Goal: area of quadrilateral {0}\n"
GOAL_GENERAL = "- Goal: value of {0}\n"
GOAL_DEFAULT = "- Goal: {0} {1}\n"

# Model answer and verifier expected answer
MODEL_ANSWER = "- Model answer: {0}\n"
VERIFIER_EXPECTED = "- Verifier expected answer: {0}\n"

# Error message headers
ERROR_HEADER = "- Error: "

# Error message constants
ERROR_UNSATISFIABLE = "Your proof contains contradictory constraints. Check for incorrect values in premises, improper theorem application, or conclusions that contradict earlier assertions.\n"
ERROR_INCOMPATIBLE = "From your proof, the verifier determines the {0} of {1} to be {2}, not {3} as you stated in your solution. Check your theorem applications and your answer.\n"
ERROR_MULTIPLE_VALUES = "Your proof doesn't uniquely determine the value. You need to use additional theorems to constrain the value.\n"
ERROR_INSUFFICIENT_INFO = "Your proof doesn't provide enough information to determine this value. You need to add theorems that specifically constrain {0} {1}.\n"
ERROR_CONTRADICTORY_CONSTRAINTS = "  Contradictory constraints:\n"
ERROR_CONSTRAINT_ITEM = "    {0}\n"

# Section headers
PREMISES_HEADER = "- Available premises:\n"
NO_GEOMETRIC_FACTS = "  No relevant geometric facts found.\n"
THEOREMS_HEADER = "- Theorems related to the goal:\n"
NO_RELATED_THEOREMS = "  None found that constrain this goal\n"
CONSTRAINTS_HEADER = "- Solver constraints directly related to this goal:\n"
NO_CONSTRAINTS = "  None found\n"
THEOREM_STEP_FORMAT = "  Step {0} - {1}({2}): {3}\n"


# Constants for premise error messages
TRIED_THEOREM = "You tried to use theorem: {0}({1});{2};{3}\n"
MISSING_PREMISE = "Missing premise: {0}\n"
DETAILS_PREFIX = "Details: {0}\n"

# Constants for trig function evaluation
TRIG_UNIQUE_VALUE = "{0}({1}) has a unique value: {2}"
CONTRADICTION_DETECTED = "Contradiction detected in evaluate_trig_function: {0}"
CALCULATED_FROM_ANGLE = "Calculated {0}({1}) = {2} from angle = {3}°"
CALCULATED_FROM_ALT_TRIG = "Calculated {0}({1}) = {2} from {3}({1}) = {4} (angle = {5}°)"
RELATED_CONSTRAINTS = "Related constraints for {0}({1}):"
CONSTRAINT_PREFIX = "  {0}"
NO_SPECIFIC_CONSTRAINTS = "No specific constraints found for {0}({1})"
NO_ANGLE_CONSTRAINTS = "No constraints found for angle {0} - insufficient information"
ANGLE_NOT_UNIQUE = "Angle {0} is not uniquely determined"
INVALID_SIN_VALUE = "Error: Invalid sin value {0} (exceeds 1)"
INVALID_COS_VALUE = "Error: Invalid cos value {0} (exceeds 1)"
ERROR_EVALUATING_ANGLE = "Error evaluating angle {0}: {1}"
ERROR_EVALUATING_TRIG = "Error evaluating {0} variable: {1}"
ERROR_CALCULATING_ALT_TRIG = "Error calculating from alternate trig function: {0}"

class ErrorTier(Enum):
    TIER1_THEOREM_CALL_SYNTAX_VIOLATION = 1  # Incorrect theorem call
    TIER2_PREMISE_VIOLATION = 2  # Premise violation
    TIER3_GOAL_NOT_REACHED = 3  # Failed to reach goal


@dataclass
class GeometricError:
    tier: ErrorTier
    message: str
    details: Optional[str] = None


@dataclass
class GeometricPoint:
    name: str


class GeometricTheorem:
    def __init__(self):

        # Solver and basic geometric elements
        self.solver = Solver()
        self.pi = Real('pi')
        self.solver.add(self.pi == 3.141592653589793)
        self.points = {}
        self.angles = {}
        self.parallel_pairs = set()
        self.perpendicular_pairs = set()
        self.collinear_facts = []
        self.theorem_sequence = []
        self.question_name = "unknown_question"
        self.defined_lines = set()
        self.mirror_congruent_triangles = []


        self.triangle_areas = {}
        self.altitude_facts = set()
        self.trapezoids = set()
        self.altitudes = {}
        self.quad_areas = {}
        self.quad_heights = {}
        self.quadrilateral_perimeters = {}
        # For handling both algebraic and numeric expressions
        self.variables = {}
        self.found_tier_1_or_2_error = False
        self.congruent_triangles = []
        self.mirror_congruent_triangles = []
        self.midsegments = set()
        self.equilateral_triangles = set()

        self.quadrilateral_diagonals = set()
        self.quadrilateral_right_angles = set()

        # Add these new attributes for length handling
        self.lengths = {}  # Store line lengths
        self.right_triangles = set()  # Add this line

        self.arcs = {}
        self.similar_triangles = []  # Store pairs of similar triangles
        self.triangle_perimeters = {}  # Store triangle perimeter values
        self.triangle_ratios = {}  # Store ratios between similar triangles
        self.added_ratio_constraints = set()

        self.mirror_similar_triangles = []  # List of canonical pairs proven mirror similar
        self.mirror_triangle_ratios = {}  # Map canonical pair -> Z3 Real variable for mirror ratio
        self.added_mirror_ratio_constraints = set()

        self.polygons = set()
        self.squares = set()
        self.rectangles = set()
        self.rhombi = set()
        self.kites = set()

        self.circle_centers = {}  # e.g. circle_centers["D"] = "D" means point D is center of circle D
        self.circle_diameters = {}  # e.g. circle_diameters["D"] = "AB" means AB is the diameter of circle D
        self.circle_radii = {}  # store radius variable for circle, e.g. circle_radii["D"] = Real("radius_D")
        self.circle_areas = {}  # store area variable for circle, e.g. circle_areas["D"] = Real("area_D")
        self.tangent_facts = set()  # e.g. set of tuples like ("AN", "O")
        self.cocircular_facts = []  # e.g. list of tuples like ("O", "B", "M")

        # 2) We'll store any 'IsDiameterOfCircle(...)' statements here
        self.is_diameter_of_circle = []  # list of (line, circleName)

        self.midsegments_of_quadrilaterals = {}
        # 3) We’ll also store any 'Cocircular(...)' facts, if needed
        self.cocircular_facts = []  # e.g. [("D", "B", "C", "A")] means D,B,C,A are on the same circle.

        # 4) For triangle area, we’ll keep a dictionary from triangle name to a Z3 Real for its area
        self.triangle_areas = {}

        # 5) We'll treat pi as a RealVal for approximate numeric checks
        from z3 import Const, RealVal, RealSort

        self.proven_area_relationships = []

        self.added_basic_constraints = set()

    def extract_variables(self, expression: str) -> Set[str]:
        """Extract variable names from an algebraic expression"""
        # Use regex to find single letters that aren't part of numbers
        variables = set(re.findall(r'(?<!\d)[a-zA-Z](?!\d)', expression))
        return variables

    def add_point(self, name: str) -> GeometricPoint:
        if name not in self.points:
            self.points[name] = GeometricPoint(name)
        return self.points[name]

    def add_angle(self, p1: str, v: str, p2: str) -> Real:
        """Return the Z3 variable for the angle with vertex v formed by p1 and p2.
           All constraints are stored in the solver."""
        normalized = self.normalize_angle_name(p1 + v + p2)
        angle_name = f"angle_{normalized}"
        if angle_name not in self.angles:
            self.angles[angle_name] = Real(angle_name)
            # Constrain the angle to be between 0 and 180.
            self.solver.add(self.angles[angle_name] > 0, self.angles[angle_name] <= 180)
        return self.angles[angle_name]

    def add_length(self, p1: str, p2: str) -> Real:
        """Return the Z3 variable for the length of the segment between p1 and p2.
           The variable is created if necessary and constrained to be nonnegative."""
        normalized = self.normalize_line_name(p1 + p2)
        length_name = f"length_{normalized}"
        if length_name not in self.lengths:
            self.lengths[length_name] = Real(length_name)
            # Add basic constraint: length >= 0.
            self.solver.add(self.lengths[length_name] > 0)
        return self.lengths[length_name]

    def create_feedback_report(self, goal_type, goal_token, model_answer, verifier_expected_answer=None,
                               status="multiple_values", additional_info=None, error_message=None,
                               related_theorems=None, relevant_constraints=None, geometric_data=None):
        """
        Create a standardized feedback report that can be used by various feedback functions.

        Parameters:
        - goal_type: Type of the goal (angle, length, arc_measure, variable, etc.)
        - goal_token: The specific token for the goal (e.g., "ABC" for an angle)
        - model_answer: The user's proposed answer
        - verifier_expected_answer: The answer computed by the verifier (if available)
        - status: Status of the verification ("unsatisfiable", "incompatible", "multiple_values", "insufficient_info")
        - additional_info: Any additional information to include
        - error_message: Custom error message (if provided)
        - related_theorems: List of theorems related to the goal
        - relevant_constraints: List of constraints relevant to the goal
        - geometric_data: Dictionary of geometric facts categorized by type

        Returns:
        - A formatted feedback report string
        """

        # Initialize the report
        report = VERIFICATION_FAILED

        # Format goal description based on type
        if goal_type != "premise_error":
            if goal_type == "angle":
                report += GOAL_ANGLE.format(goal_token)
            elif goal_type == "length":
                report += GOAL_LENGTH.format(goal_token)
            elif goal_type == "arc_measure":
                report += GOAL_ARC_MEASURE.format(goal_token)
            elif goal_type == "arc_length":
                report += GOAL_ARC_LENGTH.format(goal_token)
            elif goal_type == "cosine":
                report += GOAL_COSINE.format(goal_token)
            elif goal_type == "sine":
                report += GOAL_SINE.format(goal_token)
            elif goal_type == "sum":
                tokens = goal_token.split('+')
                report += GOAL_SUM.format(tokens[0], tokens[1])
            elif goal_type == "ratio":
                tokens = goal_token.split('/')
                report += GOAL_RATIO.format(tokens[0], tokens[1])
            elif goal_type == "perimeter":
                report += GOAL_PERIMETER.format(goal_token)
            elif goal_type == "quad_area":
                report += GOAL_QUAD_AREA.format(goal_token)
            elif goal_type == "radius":
                report += GOAL_RADIUS.format(goal_token)
            elif goal_type == "general":
                report += GOAL_GENERAL.format(goal_token)
            else:
                report += GOAL_DEFAULT.format(goal_type, goal_token)

        # Add user's answer and expected/computed value if available
        if model_answer is not None:
            report += MODEL_ANSWER.format(model_answer)

        if verifier_expected_answer is not None and status == "incompatible":
            report += VERIFIER_EXPECTED.format(verifier_expected_answer)

        # Add error message
        report += ERROR_HEADER
        if error_message:
            report += error_message
        else:
            if status == "unsatisfiable":
                report += ERROR_UNSATISFIABLE

                # Add information about contradictory constraints if available
                contradictory_constraints = self.find_contradictory_constraints()
                if contradictory_constraints:
                    report += ERROR_CONTRADICTORY_CONSTRAINTS
                    for constraint in contradictory_constraints:
                        report += ERROR_CONSTRAINT_ITEM.format(constraint)
            elif status == "incompatible":
                report += ERROR_INCOMPATIBLE.format(goal_type, goal_token, verifier_expected_answer, model_answer)
            elif status == "multiple_values":
                report += ERROR_MULTIPLE_VALUES
            elif status == "insufficient_info":
                report += ERROR_INSUFFICIENT_INFO.format(goal_type, goal_token)

        # Add all geometric facts for context
        report += PREMISES_HEADER

        if not geometric_data:
            geometric_data = self.gather_relevant_geometric_data(
                goal_variable=goal_token if goal_type == "general" else None
            )

        # Define patterns to clean up different fact categories
        category_patterns = {
            "Cocircular Points": [("Points ", "")],
            "Polygons": [("Polygon ", "")],
            "Collinear Points": [("Collinear ", "")],
            "Parallel Lines": [("Line ", "")],
            "Perpendicular Lines": [("Line ", "")],
            "Right Triangles": [("Right triangle ", "")],
            "Similar Triangles": [(" similar to ", " ~ ")],
            "Congruent Triangles": [(" congruent to ", " ≅ ")],
            "Circles": [("Circle ", ""), (" with center ", " center: ")],
            "Circle Diameters": [("Line ", ""), (" is diameter of circle ", " diameter of ")],
            "Tangent Lines": [("Line ", ""), (" is tangent to circle ", " tangent to ")],
            "Squares": [("Square ", "")],
            "Rectangles": [("Rectangle ", "")],
            "Rhombi": [("Rhombus ", "")],
            "Kites": [("Kite ", "")]
        }

        if geometric_data:
            for category, facts in geometric_data.items():
                if facts:  # Only show categories with facts
                    report += f"  {category}: "
                    cleaned_facts = []

                    for fact in facts:
                        # Clean up each fact by removing redundant prefixes
                        cleaned_fact = fact

                        # Apply all replacements for this category
                        if category in category_patterns:
                            for pattern, replacement in category_patterns[category]:
                                cleaned_fact = cleaned_fact.replace(pattern, replacement)

                        cleaned_facts.append(cleaned_fact)

                    # Join all facts with commas and add a newline at the end
                    report += f"{', '.join(cleaned_facts)}\n"
        else:
            report += NO_GEOMETRIC_FACTS

        # Add theorems related to the goal if provided
        report += THEOREMS_HEADER

        if related_theorems:
            for theorem in related_theorems:
                report += THEOREM_STEP_FORMAT.format(
                    theorem['step'],
                    theorem['theorem'],
                    ', '.join(theorem['args']),
                    theorem['conclusion']
                )
        else:
            report += NO_RELATED_THEOREMS

        # Add solver constraints
        report += CONSTRAINTS_HEADER

        if relevant_constraints:
            # Convert to list if it's a set
            if isinstance(relevant_constraints, set):
                relevant_constraints = list(relevant_constraints)

            # Sort for consistent output
            try:
                relevant_constraints.sort()
            except:
                pass  # Continue if sorting fails

            for constraint in relevant_constraints:
                report += f"  {constraint}\n"
        else:
            report += NO_CONSTRAINTS

        # Add additional information if provided
        if additional_info:
            report += f"\n{additional_info}"

        # Final message
        report += PLEASE_FIX_PROOF

        return report




    def canonicalize_mirror_triangle_pair(self, tri1: str, tri2: str) -> Tuple[str, str]:
        """
        Normalize each triangle by sorting its vertices alphabetically, then
        return a tuple of the two normalized names sorted in alphabetical order.
        For example, if tri1 = "EGH" and tri2 = "FEG":
          - "EGH" stays "EGH" (if already sorted)
          - "FEG" becomes "EFG"
          - Then the tuple is sorted to yield ("EFG", "EGH")
        """
        tri1_norm = ''.join(sorted(tri1.strip().upper()))
        tri2_norm = ''.join(sorted(tri2.strip().upper()))
        return tuple(sorted([tri1_norm, tri2_norm]))

    def canonicalize_mirror_congruent_triangle_pair(self, tri1: str, tri2: str) -> Tuple[str, str]:
        """
        Normalize triangles for mirror congruence checking.
        For mirror congruent triangles, we consider rotations only.
        """
        # For first triangle, generate all rotations
        rotations1 = [tri1[i:] + tri1[:i] for i in range(len(tri1))]

        # For second triangle, generate all rotations
        rotations2 = [tri2[i:] + tri2[:i] for i in range(len(tri2))]

        # Find the lexicographically smallest pair
        canonical_pair = min((r1, r2) for r1 in rotations1 for r2 in rotations2)

        return canonical_pair

    def find_contradictory_constraints(self, max_constraints=10):
        """
        Find a small subset of constraints that are contradictory using Z3's unsat core feature.

        Args:
            max_constraints: Maximum number of constraints to return

        Returns:
            list: A list of formatted contradictory constraints
        """
        from z3 import Solver, unsat, Bool

        # Get all assertions from the current solver
        assertions = list(self.solver.assertions())

        # Create a new solver for unsat core tracking
        core_solver = Solver()
        tracking = {}

        # Add each assertion with a tracking variable
        for i, a in enumerate(assertions):
            a_str = str(a)

            # Skip pi constant definitions and basic bounds constraints
            if any(x in a_str for x in ["pi ==", "angle_ > 0", "angle_ <= 180", "length_ > 0",
                                        "arc_ >= 0", "arc_ <= 360", ">= -1", "<= 1"]):
                continue

            # Create a tracking variable
            track_var = Bool(f"track_{i}")
            tracking[track_var] = a
            core_solver.assert_and_track(a, track_var)

        # Check if still unsat and get the core
        if core_solver.check() == unsat:
            core = core_solver.unsat_core()

            # Convert core to original assertions
            contradiction = []
            for var in core:
                if var in tracking:
                    constraint = self.format_constraint(str(tracking[var]))
                    if constraint not in contradiction:
                        contradiction.append(constraint)

            # Limit the number of constraints returned
            return contradiction[:max_constraints]

        return []  # If not unsatisfiable with the filtered set



    def canonicalize_congruent_triangle_pair(self, tri1: str, tri2: str) -> Tuple[str, str]:
        """
        Normalize triangles for congruence checking.
        For congruent triangles, we need to consider all possible rotations of both triangles
        and their reflections (since congruence preserves orientation).
        """
        # For first triangle, generate all rotations
        rotations1 = [tri1[i:] + tri1[:i] for i in range(len(tri1))]

        # For second triangle, generate all rotations
        rotations2 = [tri2[i:] + tri2[:i] for i in range(len(tri2))]

        # Also consider all rotations of reversed second triangle (for reflections)
        rev_tri2 = tri2[::-1]
        rotations2_rev = [rev_tri2[i:] + rev_tri2[:i] for i in range(len(rev_tri2))]

        # Combine all possible rotations of the second triangle
        all_rotations2 = rotations2 + rotations2_rev

        # Find the lexicographically smallest pair
        canonical_pair = min((r1, r2) for r1 in rotations1 for r2 in all_rotations2)

        return canonical_pair

    def collect_variable_references(self, variable_name, max_constraints=50):
        """
        Collect all references to a specific variable in the proof using a generalized approach.

        Args:
            variable_name (str): The name of the variable to search for (e.g., 'p')
            max_constraints (int): Maximum number of constraints to collect

        Returns:
            dict: A dictionary containing different types of references to the variable
        """
        references = {
            "angle_expressions": [],  # Expressions like MeasureOfAngle(ABC) = 3*p+5
            "length_expressions": [],  # Expressions like LengthOfLine(AB) = 2*p
            "arc_expressions": [],  # Expressions like MeasureOfArc(ABC) = p+10
            "algebraic_constraints": [],  # Direct algebraic constraints like p = 25
            "solver_constraints": [],  # Z3 solver constraints involving p
            "related_constraints": [],  # Related constraints between variables
            "related_theorems": []  # Theorems that establish values related to p
        }

        # Regular expression to match the variable as a standalone identifier
        var_pattern = re.compile(r'(^|[^a-zA-Z0-9_])' + re.escape(variable_name) + r'([^a-zA-Z0-9_]|$)')

        # 1. Search TEXT_CDL section if available
        if hasattr(self, 'text_cdl_lines'):
            for line in self.text_cdl_lines:
                # Look for angle expressions containing the variable
                angle_match = re.search(r'Equal\(MeasureOfAngle\((\w+)\),(.*?)\)', line)
                if angle_match and var_pattern.search(angle_match.group(2)):
                    angle_name, expr = angle_match.groups()
                    references["angle_expressions"].append(f"∠{angle_name} = {expr.strip()}")

                # Look for length expressions containing the variable
                length_match = re.search(r'Equal\(LengthOfLine\((\w+)\),(.*?)\)', line)
                if length_match and var_pattern.search(length_match.group(2)):
                    line_name, expr = length_match.groups()
                    references["length_expressions"].append(f"|{line_name}| = {expr.strip()}")

                # Look for arc expressions containing the variable
                arc_match = re.search(r'Equal\(MeasureOfArc\((\w+)\),(.*?)\)', line)
                if arc_match and var_pattern.search(arc_match.group(2)):
                    arc_name, expr = arc_match.groups()
                    references["arc_expressions"].append(f"arc {arc_name} = {expr.strip()}")

                # Look for direct algebraic constraints on the variable
                direct_match = re.search(rf'Equal\({variable_name},(.*?)\)', line)
                if direct_match:
                    references["algebraic_constraints"].append(f"{variable_name} = {direct_match.group(1).strip()}")
                elif re.search(rf'{variable_name}\s*=', line):
                    references["algebraic_constraints"].append(line.strip())

        # 2. Use our new generalized constraint finder
        try:
            relevant_constraints = self.find_relevant_constraints(variable_name)
            references["solver_constraints"] = relevant_constraints["direct_constraints"]
            references["related_constraints"] = relevant_constraints["related_constraints"]
        except Exception as e:
            print(f"Error finding constraints: {e}")
            # If general approach fails, provide a simple fallback
            for c in self.solver.assertions():
                c_str = str(c)
                if var_pattern.search(c_str) and "pi ==" not in c_str:
                    references["solver_constraints"].append(self.format_constraint(c_str))

        # 3. Check theorem sequence for conclusions involving the variable
        for theorem_info in self.theorem_sequence:
            for conclusion in theorem_info["conclusions"]:
                if var_pattern.search(conclusion):
                    references["related_theorems"].append({
                        "step": theorem_info["step_number"],
                        "theorem": theorem_info["theorem_name"],
                        "args": theorem_info["args"],
                        "conclusion": conclusion
                    })
                    break  # Only add each theorem once

            # Also check premises for the variable
            if var_pattern.search(theorem_info["premise"]):
                # Add this as a related theorem since the variable appears in the premise
                if not any(t["step"] == theorem_info["step_number"] for t in references["related_theorems"]):
                    references["related_theorems"].append({
                        "step": theorem_info["step_number"],
                        "theorem": theorem_info["theorem_name"],
                        "args": theorem_info["args"],
                        "conclusion": "Variable in premise: " + theorem_info["premise"]
                    })

        return references

    def get_direct_variable_constraints(self, variable_name):
        """
        A simpler, more efficient approach to get just the algebraic constraints on a variable.
        This should be fast even with many angles and assertions.
        """
        constraints = []

        # Regular expression to match the variable as a standalone identifier
        var_pattern = re.compile(r'(^|[^a-zA-Z0-9_])' + re.escape(variable_name) + r'([^a-zA-Z0-9_]|$)')

        # 1. Check TEXT_CDL for direct expressions with the variable
        if hasattr(self, 'text_cdl_lines'):
            for line in self.text_cdl_lines:
                if var_pattern.search(line):
                    # Angle expressions
                    angle_match = re.search(r'Equal\(MeasureOfAngle\((\w+)\),(.*?)\)', line)
                    if angle_match and var_pattern.search(angle_match.group(2)):
                        angle_name, expr = angle_match.groups()
                        constraints.append(f"∠{angle_name} = {expr.strip()}")
                        continue

                    # Length expressions
                    length_match = re.search(r'Equal\(LengthOfLine\((\w+)\),(.*?)\)', line)
                    if length_match and var_pattern.search(length_match.group(2)):
                        line_name, expr = length_match.groups()
                        constraints.append(f"|{line_name}| = {expr.strip()}")
                        continue

                    # Direct variable assignments
                    direct_match = re.search(rf'Equal\({variable_name},(.*?)\)', line)
                    if direct_match:
                        constraints.append(f"{variable_name} = {direct_match.group(1).strip()}")
                        continue

                    # Basic assignment (variable = value)
                    simple_match = re.search(rf'{variable_name}\s*=\s*(.*?)(?:$|[,);])', line)
                    if simple_match:
                        constraints.append(f"{variable_name} = {simple_match.group(1).strip()}")
                        continue

        # 2. For the theorem sequence, just show theorems that establish equations with the variable
        for theorem_info in self.theorem_sequence:
            for conclusion in theorem_info["conclusions"]:
                if "Equal" in conclusion and var_pattern.search(conclusion):
                    constraints.append(
                        f"Step {theorem_info['step_number']} - {theorem_info['theorem_name']} establishes: {conclusion}"
                    )
                    break

        return constraints

    def format_constraint(self, constraint_str):
        """
        Format a Z3 constraint string to be more readable.

        Args:
            constraint_str (str): The original constraint string from Z3

        Returns:
            str: A more readable formatted constraint
        """
        # Skip if this is a comment or special marker
        if constraint_str.startswith('#'):
            return constraint_str

        # Remove leading "0 + " that commonly appears in sum expressions
        constraint_str = re.sub(r'^0\s*\+\s*', '', constraint_str)

        # Replace angle_ABC with ∠ABC for better readability, but be careful of word boundaries
        constraint_str = re.sub(r'(^|[^a-zA-Z0-9_])angle_(\w+)', r'\1∠\2', constraint_str)

        # Replace length_AB with |AB| for better readability
        constraint_str = re.sub(r'(^|[^a-zA-Z0-9_])length_(\w+)', r'\1|\2|', constraint_str)

        # Replace arc_ABC with arc(ABC) for better readability
        constraint_str = re.sub(r'(^|[^a-zA-Z0-9_])arc_(\w+)', r'\1arc(\2)', constraint_str)

        # Replace common Z3 operators
        constraint_str = constraint_str.replace(' == ', ' = ')
        constraint_str = constraint_str.replace(' + ', ' + ')
        constraint_str = constraint_str.replace(' - ', ' - ')
        constraint_str = constraint_str.replace(' * ', ' × ')
        constraint_str = constraint_str.replace(' / ', ' ÷ ')

        # Remove leading/trailing spaces
        constraint_str = constraint_str.strip()

        return constraint_str




    def gather_relevant_geometric_data(self, excluded_categories=None, goal_variable=None):
        """
        Collect all non-empty geometric facts that might be relevant for feedback.

        Args:
            excluded_categories: List of category names to exclude from the output
            goal_variable: If specified, filter facts to only show those relevant to this variable
        """
        if excluded_categories is None:
            excluded_categories = []  # Don't exclude any categories by default

        geometric_data = {}

        # Get related angles and lengths if goal_variable is provided
        related_points = set()
        if goal_variable and hasattr(self, 'text_cdl_lines'):
            for line in self.text_cdl_lines:
                if goal_variable in line:
                    # Extract angle points related to goal variable
                    angle_match = re.search(r'Equal\(MeasureOfAngle\((\w+)\),(.*?)\)', line)
                    if angle_match and goal_variable in angle_match.group(2):
                        angle_points = angle_match.group(1)
                        for point in angle_points:
                            related_points.add(point)

                    # Extract length points related to goal variable
                    length_match = re.search(r'Equal\(LengthOfLine\((\w+)\),(.*?)\)', line)
                    if length_match and goal_variable in length_match.group(2):
                        length_points = length_match.group(1)
                        for point in length_points:
                            related_points.add(point)

        # Parallel lines - with proper deduplication
        if self.parallel_pairs:
            formatted_pairs = set()
            for p1, p2 in self.parallel_pairs:
                # Normalize each line by sorting characters within the line
                line1 = ''.join(sorted(p1))
                line2 = ''.join(sorted(p2))

                # Normalize the pair by sorting the normalized lines
                sorted_pair = tuple(sorted([line1, line2]))
                formatted_pairs.add(f"{sorted_pair[0]} ∥ {sorted_pair[1]}")

            if formatted_pairs and "Parallel Lines" not in excluded_categories:
                geometric_data["Parallel Lines"] = sorted(formatted_pairs)

        # Perpendicular lines - with proper deduplication
        if self.perpendicular_pairs:
            formatted_pairs = set()
            for p1, p2 in self.perpendicular_pairs:
                # Normalize each line by sorting characters within the line
                line1 = ''.join(sorted(p1))
                line2 = ''.join(sorted(p2))

                # Normalize the pair by sorting the normalized lines
                sorted_pair = tuple(sorted([line1, line2]))
                formatted_pairs.add(f"{sorted_pair[0]} ⊥ {sorted_pair[1]}")

            if formatted_pairs and "Perpendicular Lines" not in excluded_categories:
                geometric_data["Perpendicular Lines"] = sorted(formatted_pairs)

        # Collinear facts - filter by relevant points if goal_variable provided
        if self.collinear_facts and "Collinear Points" not in excluded_categories:
            filtered_facts = []

            for points in self.collinear_facts:
                # If we have a goal variable, only include collinear facts containing related points
                if goal_variable and related_points:
                    if any(p in related_points for p in points):
                        filtered_facts.append(f"Collinear {''.join(points)}")
                else:
                    # Otherwise include all collinear facts
                    filtered_facts.append(f"Collinear {''.join(points)}")

            if filtered_facts:
                geometric_data["Collinear Points"] = sorted(set(filtered_facts))

        # Right triangles
        if self.right_triangles and "Right Triangles" not in excluded_categories:
            formatted_triangles = [f"Right triangle {tri}" for tri in self.right_triangles]
            if formatted_triangles:
                geometric_data["Right Triangles"] = sorted(set(formatted_triangles))

        # Similar triangles
        if self.similar_triangles and "Similar Triangles" not in excluded_categories:
            formatted_pairs = [f"{tri1} similar to {tri2}" for tri1, tri2 in self.similar_triangles]
            if formatted_pairs:
                geometric_data["Similar Triangles"] = sorted(set(formatted_pairs))

        # Congruent triangles
        if hasattr(self,
                   'congruent_triangles') and self.congruent_triangles and "Congruent Triangles" not in excluded_categories:
            formatted_pairs = [f"{tri1} congruent to {tri2}" for tri1, tri2 in self.congruent_triangles]
            if formatted_pairs:
                geometric_data["Congruent Triangles"] = sorted(set(formatted_pairs))

        # Mirror Congruent triangles
        if hasattr(self,
                   'mirror_congruent_triangles') and self.mirror_congruent_triangles and "Mirror Congruent Triangles" not in excluded_categories:
            formatted_pairs = [f"{tri1} mirror congruent to {tri2}" for tri1, tri2 in self.mirror_congruent_triangles]
            if formatted_pairs:
                geometric_data["Mirror Congruent Triangles"] = sorted(set(formatted_pairs))

        # Mirror Similar triangles
        if hasattr(self,
                   'mirror_similar_triangles') and self.mirror_similar_triangles and "Mirror Similar Triangles" not in excluded_categories:
            formatted_pairs = [f"{tri1} mirror similar to {tri2}" for tri1, tri2 in self.mirror_similar_triangles]
            if formatted_pairs:
                geometric_data["Mirror Similar Triangles"] = sorted(set(formatted_pairs))

        # Cocircular facts
        if hasattr(self,
                   'cocircular_facts') and self.cocircular_facts and "Cocircular Points" not in excluded_categories:
            formatted_cocircular = []
            for fact in self.cocircular_facts:
                if fact and len(fact) > 1:
                    circle = fact[0]
                    points = ''.join(fact[1:])
                    formatted_cocircular.append(f"Points {points} on circle {circle}")
            if formatted_cocircular:
                geometric_data["Cocircular Points"] = sorted(set(formatted_cocircular))

        # Circles
        if hasattr(self, 'circle_centers') and self.circle_centers and "Circles" not in excluded_categories:
            formatted_centers = [f"Circle {circle} with center {center}" for circle, center in
                                 self.circle_centers.items()]
            if formatted_centers:
                geometric_data["Circles"] = sorted(set(formatted_centers))

        # Circle diameters
        if hasattr(self,
                   'is_diameter_of_circle') and self.is_diameter_of_circle and "Circle Diameters" not in excluded_categories:
            formatted_diameters = [f"Line {line} is diameter of circle {circle}" for line, circle in
                                   self.is_diameter_of_circle]
            if formatted_diameters:
                geometric_data["Circle Diameters"] = sorted(set(formatted_diameters))

        # Tangent facts
        if hasattr(self, 'tangent_facts') and self.tangent_facts and "Tangent Lines" not in excluded_categories:
            formatted_tangents = [f"Line {line} is tangent to circle {circle}" for line, circle in self.tangent_facts]
            if formatted_tangents:
                geometric_data["Tangent Lines"] = sorted(set(formatted_tangents))

        # Squares
        if hasattr(self, 'squares') and self.squares and "Squares" not in excluded_categories:
            formatted_squares = [f"Square {square}" for square in self.squares]
            if formatted_squares:
                geometric_data["Squares"] = sorted(set(formatted_squares))

        # Rectangles
        if hasattr(self, 'rectangles') and self.rectangles and "Rectangles" not in excluded_categories:
            formatted_rectangles = [f"Rectangle {rect}" for rect in self.rectangles]
            if formatted_rectangles:
                geometric_data["Rectangles"] = sorted(set(formatted_rectangles))

        # Rhombi
        if hasattr(self, 'rhombi') and self.rhombi and "Rhombi" not in excluded_categories:
            formatted_rhombi = [f"Rhombus {rhom}" for rhom in self.rhombi]
            if formatted_rhombi:
                geometric_data["Rhombi"] = sorted(set(formatted_rhombi))

        # Kites
        if hasattr(self, 'kites') and self.kites and "Kites" not in excluded_categories:
            formatted_kites = [f"Kite {kite}" for kite in self.kites]
            if formatted_kites:
                geometric_data["Kites"] = sorted(set(formatted_kites))

        # Polygons
        if self.polygons and "Polygons" not in excluded_categories:
            formatted_polygons = [f"Polygon {poly}" for poly in self.polygons]
            if formatted_polygons:
                geometric_data["Polygons"] = sorted(set(formatted_polygons))

        # Remove empty categories
        return {k: v for k, v in geometric_data.items() if v}

    def evaluate_trig_function(self, func_name, angle_token, model_answer):
        """
        Evaluates a trigonometric function (sin/cos) for an angle.
        Provides better error handling and feedback for contradictions.

        Args:
            func_name: Either "sin" or "cos"
            angle_token: The angle name (e.g., "BAC")
            model_answer: The expected answer to verify

        Returns:
            tuple of (success, value, status)
        """
        import math
        epsilon = 1e-8  # Common epsilon value for all goals

        # First, try to get the angle variable directly
        angle_var = self.add_angle(angle_token[0], angle_token[1], angle_token[2])

        # Create or get the trig function variable if it exists
        trig_var_name = f"{func_name}_{angle_token}"
        if trig_var_name not in self.variables:
            self.variables[trig_var_name] = Real(trig_var_name)
            # Add bounds for sine/cosine
            self.solver.add(self.variables[trig_var_name] >= -1)
            self.solver.add(self.variables[trig_var_name] <= 1)

        trig_var = self.variables[trig_var_name]

        # Check if the system is satisfiable
        check_result = self.solver.check()

        if check_result == unsat:
            # System is unsatisfiable - there's a contradiction
            contradictory_constraints = self.find_contradictory_constraints()
            details = "No specific contradictory constraints found."

            if contradictory_constraints:
                details = ERROR_CONTRADICTORY_CONSTRAINTS
                for constraint in contradictory_constraints:
                    details += ERROR_CONSTRAINT_ITEM.format(constraint)

            print(CONTRADICTION_DETECTED.format(details))
            return False, None, "unsatisfiable"

        elif check_result == sat:
            model = self.solver.model()

            # First approach: Check if the trig function variable already has a value
            try:
                trig_val_str = model.eval(trig_var).as_decimal(10)
                if trig_val_str.endswith('?'):
                    trig_val_str = trig_val_str[:-1]
                trig_val = float(trig_val_str)

                # Check if this value is uniquely determined
                temp_solver = Solver()
                for c in self.solver.assertions():
                    temp_solver.add(c)

                temp_solver.add(Or(trig_var < trig_val - epsilon, trig_var > trig_val + epsilon))

                if temp_solver.check() == unsat:
                    # Value is uniquely determined
                    print(TRIG_UNIQUE_VALUE.format(func_name, angle_token, trig_val))
                    if abs(trig_val - model_answer) < epsilon:
                        return True, trig_val, "unique"
                    else:
                        return False, trig_val, "incompatible"
            except Exception as e:
                print(ERROR_EVALUATING_TRIG.format(func_name, e))

            # Second approach: Try to calculate from the angle if it exists
            try:
                angle_val_str = model.eval(angle_var).as_decimal(10)
                if angle_val_str.endswith('?'):
                    angle_val_str = angle_val_str[:-1]
                angle_val = float(angle_val_str)

                # Check if angle is uniquely determined
                temp_solver = Solver()
                for c in self.solver.assertions():
                    temp_solver.add(c)

                temp_solver.add(Or(angle_var < angle_val - epsilon, angle_var > angle_val + epsilon))

                if temp_solver.check() == unsat:
                    # Angle is uniquely determined, calculate trig function
                    if func_name == "sin":
                        calculated_val = math.sin(math.radians(angle_val))
                    else:  # cos
                        calculated_val = math.cos(math.radians(angle_val))

                    print(CALCULATED_FROM_ANGLE.format(func_name, angle_token, calculated_val, angle_val))

                    if abs(calculated_val - model_answer) < epsilon:
                        return True, calculated_val, "unique"
                    else:
                        return False, calculated_val, "incompatible"
                else:
                    print(ANGLE_NOT_UNIQUE.format(angle_token))
            except Exception as e:
                print(ERROR_EVALUATING_ANGLE.format(angle_token, e))

            # Third approach: Try to calculate from the alternate trig function
            alt_func_name = "cos" if func_name == "sin" else "sin"
            alt_trig_var_name = f"{alt_func_name}_{angle_token}"

            if alt_trig_var_name in self.variables:
                alt_trig_var = self.variables[alt_trig_var_name]

                try:
                    # Get the alternate trig value from the model
                    alt_trig_val_str = model.eval(alt_trig_var).as_decimal(10)
                    if alt_trig_val_str.endswith('?'):
                        alt_trig_val_str = alt_trig_val_str[:-1]
                    alt_trig_val = float(alt_trig_val_str)

                    # Check if the alternate trig value is uniquely determined
                    temp_solver = Solver()
                    for c in self.solver.assertions():
                        temp_solver.add(c)

                    temp_solver.add(Or(alt_trig_var < alt_trig_val - epsilon, alt_trig_var > alt_trig_val + epsilon))

                    if temp_solver.check() == unsat:
                        # Alternate trig value is uniquely determined
                        # Calculate the angle from the alternate trig function
                        import math

                        # Get the angle (in degrees) from the alternate trig function
                        if alt_func_name == "sin":
                            # If we have sin, use arcsin
                            if abs(alt_trig_val) > 1:
                                print(INVALID_SIN_VALUE.format(alt_trig_val))
                                return False, None, "multiple_values"
                            angle_in_degrees = math.degrees(math.asin(alt_trig_val))
                        else:  # alt_func_name == "cos"
                            # If we have cos, use arccos
                            if abs(alt_trig_val) > 1:
                                print(INVALID_COS_VALUE.format(alt_trig_val))
                                return False, None, "multiple_values"
                            angle_in_degrees = math.degrees(math.acos(alt_trig_val))

                        # Handle multiple possible angles (arcsin/arccos can have multiple solutions)
                        possible_angles = [angle_in_degrees]
                        if alt_func_name == "sin":
                            # If sin(θ) = k, then sin(180-θ) = k as well
                            possible_angles.append(180 - angle_in_degrees)
                        else:  # alt_func_name == "cos"
                            # If cos(θ) = k, then cos(360-θ) = k as well
                            possible_angles.append(360 - angle_in_degrees)

                        # Try each possible angle
                        for angle_val in possible_angles:
                            # Calculate the requested trig function using the determined angle
                            if func_name == "sin":
                                calculated_val = math.sin(math.radians(angle_val))
                            else:  # func_name == "cos"
                                calculated_val = math.cos(math.radians(angle_val))

                            print(CALCULATED_FROM_ALT_TRIG.format(
                                func_name, angle_token, calculated_val, alt_func_name, alt_trig_val, angle_val
                            ))

                            # Check if this calculated value matches the expected answer
                            if abs(calculated_val - model_answer) < epsilon:
                                return True, calculated_val, "unique"

                        # If we get here, none of the calculated values matched
                        return False, calculated_val, "incompatible"

                except Exception as e:
                    print(ERROR_CALCULATING_ALT_TRIG.format(e))

            # Provide better feedback on why it's not uniquely determined
            related_constraints = []
            for c in self.solver.assertions():
                c_str = str(c)
                if f"{func_name}_{angle_token}" in c_str or f"angle_{angle_token}" in c_str:
                    related_constraints.append(self.format_constraint(c_str))

            if related_constraints:
                print(RELATED_CONSTRAINTS.format(func_name, angle_token))
                for constraint in related_constraints:
                    print(CONSTRAINT_PREFIX.format(constraint))
            else:
                print(NO_SPECIFIC_CONSTRAINTS.format(func_name, angle_token))

            # Check if we have any constraints on the angle at all
            angle_constraints = []
            for c in self.solver.assertions():
                c_str = str(c)
                if f"angle_{angle_token}" in c_str:
                    angle_constraints.append(self.format_constraint(c_str))

            if not angle_constraints:
                print(NO_ANGLE_CONSTRAINTS.format(angle_token))
                return False, None, "insufficient_info"

            # If we get here, we couldn't determine the value from any method
            return False, None, "multiple_values"
        else:
            return False, None, "unknown"

    def normalize_quadrilateral(self, quad_name: str) -> str:
        """
        Normalize a quadrilateral name to handle different permutations.
        For a quadrilateral, we find all cyclic permutations and return the
        lexicographically smallest one.
        """
        # Get all cyclic permutations
        permutations = []
        n = len(quad_name)
        for i in range(n):
            permutation = quad_name[i:] + quad_name[:i]
            permutations.append(permutation)

        # Return the lexicographically smallest permutation
        return min(permutations)

    def is_midsegment_of_quadrilateral(self, segment: str, quad: str) -> bool:
        """
        Check if the given segment is stored as a midsegment of the given quadrilateral.
        This handles normalization of the quadrilateral name.
        """
        # Normalize quadrilateral name
        norm_quad = self.normalize_quadrilateral(quad)

        # Check all permutations of the segment (FE vs EF)
        segments = [segment, segment[::-1]]

        # Check if any combination exists in our stored midsegments
        for seg in segments:
            if (seg, norm_quad) in self.midsegments_of_quadrilaterals:
                return True

        return False

    def identify_midsegment_quadrilateral(self, segment: str, quad: str) -> bool:
        """
        Check if a segment can be identified as a midsegment of a quadrilateral
        by analyzing if it connects midpoints of opposite sides.
        """
        if len(segment) != 2 or len(quad) != 4:
            return False

        # Check if we have midpoint information about the segment endpoints
        e_midpoint_of = []
        f_midpoint_of = []

        # Use previously established midpoint information
        if hasattr(self, "midpoints"):
            for (p1, p2), midpoint in self.midpoints.items():
                if midpoint == segment[0]:  # First point of segment (e.g., "E")
                    e_midpoint_of.append((p1, p2))
                elif midpoint == segment[1]:  # Second point of segment (e.g., "F")
                    f_midpoint_of.append((p1, p2))

        # If we don't have enough midpoint information, return False
        if not e_midpoint_of or not f_midpoint_of:
            return False

        # Get the sides of the quadrilateral (in order)
        sides = [
            (quad[0], quad[1]),
            (quad[1], quad[2]),
            (quad[2], quad[3]),
            (quad[3], quad[0])
        ]

        # Convert sides to sets for easier comparison (AB == BA)
        sides_sets = [set(side) for side in sides]

        # Check if E and F are midpoints of opposite sides
        for e_side in e_midpoint_of:
            e_side_set = set(e_side)
            e_side_idx = -1

            # Find which side E is the midpoint of
            for i, side_set in enumerate(sides_sets):
                if e_side_set == side_set:
                    e_side_idx = i
                    break

            if e_side_idx == -1:
                continue

            # Check if F is the midpoint of the opposite side
            opposite_idx = (e_side_idx + 2) % 4
            opposite_side_set = sides_sets[opposite_idx]

            for f_side in f_midpoint_of:
                if set(f_side) == opposite_side_set:
                    return True

        return False

    def check_midsegment_with_permutations(self, segment: str, quad: str) -> bool:
        """
        Check if a segment is a midsegment of a quadrilateral considering all
        possible permutations of the quadrilateral.
        """
        # Check all cyclic permutations of the quadrilateral
        for i in range(len(quad)):
            perm = quad[i:] + quad[:i]

            # Check both segment orientations
            if self.is_midsegment_of_quadrilateral(segment, perm) or \
                    self.is_midsegment_of_quadrilateral(segment[::-1], perm):
                return True

            # Also try to identify it geometrically
            if self.identify_midsegment_quadrilateral(segment, perm) or \
                    self.identify_midsegment_quadrilateral(segment[::-1], perm):
                # If identified, store it for future reference
                norm_quad = self.normalize_quadrilateral(perm)
                self.midsegments_of_quadrilaterals[(segment, norm_quad)] = True
                self.midsegments_of_quadrilaterals[(segment[::-1], norm_quad)] = True
                return True

        return False

    def get_opposite_sides_of_quadrilateral(self, quad: str) -> list:
        """
        Get the pairs of opposite sides in a quadrilateral.
        """
        if len(quad) != 4:
            return []

        # For a quadrilateral with vertices in cyclic order A,B,C,D:
        # - Side 1: AB, Side 2: BC, Side 3: CD, Side 4: DA
        # - Opposite sides are: (AB, CD) and (BC, DA)
        sides = [
            (quad[0] + quad[1], quad[2] + quad[3]),  # Sides 1 and 3
            (quad[1] + quad[2], quad[3] + quad[0])  # Sides 2 and 4
        ]

        return sides

    def add_mirror_similar_triangles(self, tri1: str, tri2: str):
        """Record that triangles tri1 and tri2 are mirror similar (by AA)
        and create a corresponding ratio variable if not already defined."""
        canonical_pair = self.canonicalize_mirror_triangle_pair(tri1, tri2)

        if canonical_pair not in self.mirror_similar_triangles:
            self.mirror_similar_triangles.append(canonical_pair)
            print(f"Recorded mirror similarity for triangles: {canonical_pair}")
        if canonical_pair not in self.mirror_triangle_ratios:
            var_name = f"ratio_mirror_{canonical_pair[0]}_{canonical_pair[1]}"
            self.mirror_triangle_ratios[canonical_pair] = Real(var_name)
            print(f"Created mirror similar ratio variable: {var_name}")
        # self.add_all_side_mirror_ratio_constraints(tri1, tri2)

    def generate_detailed_feedback(self, goal_type, goal_token, model_answer, verifier_expected_answer=None,
                                   status="multiple_values", additional_info=None):
        """Generate feedback in the user's preferred format with improved content filtering."""

        # Find theorems directly related to the goal
        related_theorems = []

        for theorem_info in self.theorem_sequence:
            is_related = False

            # Check for direct mention of the goal in conclusions
            for conclusion in theorem_info["conclusions"]:
                if goal_token in conclusion:
                    is_related = True
                    break

                # Check more carefully depending on goal type
                if not is_related and goal_type in ["angle", "arc_measure", "arc_length", "sine", "cosine"]:
                    for conclusion in theorem_info["conclusions"]:
                        pattern = rf'(MeasureOf(Angle|Arc)|Sin|Cos)\((\w+)\)'
                        matches = re.findall(pattern, conclusion)
                        for match in matches:
                            if match[1] == goal_token or set(match[1]) == set(goal_token):
                                is_related = True
                                break

            # Check if mentioned in the premise
            if goal_token in theorem_info["premise"]:
                is_related = True

            # Check if mentioned in args
            if any(goal_token in arg for arg in theorem_info["args"]):
                is_related = True

            if is_related:
                related_theorems.append({
                    "step": theorem_info["step_number"],
                    "theorem": theorem_info["theorem_name"],
                    "args": theorem_info["args"],
                    "conclusion": ", ".join(theorem_info["conclusions"])
                })

        # Determine appropriate variable names based on goal type for constraints
        var_names = []
        if goal_type == "arc_length":
            var_names.append(f"lengthArc_{self.normalize_arc(goal_token)}")
            var_names.append(f"arc_{self.normalize_arc(goal_token)}")
        elif goal_type == "arc_measure":
            var_names.append(f"arc_{self.normalize_arc(goal_token)}")
        elif goal_type == "length":
            var_names.append(f"length_{self.normalize_line_name(goal_token)}")
        elif goal_type == "angle":
            var_names.append(f"angle_{self.normalize_angle_name(goal_token)}")
        elif goal_type == "cosine":
            var_names.append(f"cos_{goal_token}")
            var_names.append(f"angle_{self.normalize_angle_name(goal_token)}")
        elif goal_type == "sine":
            var_names.append(f"sin_{goal_token}")
            var_names.append(f"angle_{self.normalize_angle_name(goal_token)}")
        elif goal_type == "sum":
            tokens = goal_token.split('+')
            for token in tokens:
                var_names.append(f"length_{self.normalize_line_name(token)}")
        elif goal_type == "ratio":
            tokens = goal_token.split('/')
            for token in tokens:
                var_names.append(f"length_{self.normalize_line_name(token)}")
        elif goal_type == "perimeter":
            var_names.append(f"perimeter_{goal_token}")
        elif goal_type == "quad_area":
            var_names.append(f"AreaOfQuadrilateral_{goal_token}")

        # Use a set to track unique constraints
        unique_constraints = set()

        for c in self.solver.assertions():
            c_str = str(c)
            for var_name in var_names:
                if var_name in c_str:
                    # Format constraint for readability
                    formatted = self.format_constraint(c_str)
                    unique_constraints.add(formatted)
                    break

        # Convert to list and sort for consistent output
        relevant_constraints = sorted(list(unique_constraints))

        # Use the common feedback report function
        return self.create_feedback_report(
            goal_type=goal_type,
            goal_token=goal_token,
            model_answer=model_answer,
            verifier_expected_answer=verifier_expected_answer,
            status=status,
            additional_info=additional_info,
            related_theorems=related_theorems,
            relevant_constraints=relevant_constraints
        )

    # Second function: Update for variable goals specifically
    def generate_detailed_feedback_for_variable(self, variable_name, model_answer, verifier_expected_answer=None,
                                                status="multiple_values"):
        """Generate detailed feedback specifically for a variable goal with improved formatting."""

        # Get direct constraints for the variable
        direct_constraints = self.get_direct_variable_constraints(variable_name)

        # Get geometric facts filtered to show only those relevant to this variable
        geometric_data = self.gather_relevant_geometric_data(goal_variable=variable_name)

        # Get related theorems
        related_theorems = self.find_related_theorems_for_variable(variable_name)

        # Get solver constraints
        try:
            result = self.find_relevant_constraints(variable_name)
            # Add direct constraints first
            unique_constraints = set(result["direct_constraints"])
            # Then add related constraints
            for constraint in result["related_constraints"]:
                unique_constraints.add(constraint)

            # Convert to list and sort
            all_constraints = list(unique_constraints)

            def constraint_sort_key(constraint):
                priority = 0 if variable_name in constraint else 1
                return (priority, constraint)

            all_constraints.sort(key=constraint_sort_key)
        except Exception as e:
            print(f"Error finding constraints: {e}")
            all_constraints = [f"Error finding constraints: {e}"]

        # Add contradictory constraints if needed
        contradictory_constraints = None
        if status == "unsatisfiable":
            contradictory_constraints = self.find_contradictory_constraints()

        # Create custom error message for unsatisfiable case
        error_message = None
        if status == "unsatisfiable" and contradictory_constraints:
            error_message = ERROR_UNSATISFIABLE
            error_message += ERROR_CONTRADICTORY_CONSTRAINTS
            for constraint in contradictory_constraints:
                error_message += ERROR_CONSTRAINT_ITEM.format(constraint)

        # Create additional info section for equations if relevant
        additional_info = None
        if direct_constraints:
            additional_info = "Equations with this variable:\n"
            for constraint in direct_constraints:
                additional_info += f"  {constraint}\n"

        # Use the common feedback report function
        return self.create_feedback_report(
            goal_type="general",
            goal_token=variable_name,
            model_answer=model_answer,
            verifier_expected_answer=verifier_expected_answer,
            status=status,
            additional_info=additional_info,
            error_message=error_message,
            related_theorems=related_theorems,
            relevant_constraints=all_constraints,
            geometric_data=geometric_data
        )

    def find_relevant_constraints(self, variable_name, max_constraints=200):
        """
        Find all constraints relevant to a variable.
        This will find both direct constraints and constraints on related variables.

        Args:
            variable_name (str): The name of the variable to search for
            max_constraints (int): Maximum number of constraints to return

        Returns:
            dict: Dictionary with direct and related constraints
        """
        result = {
            "direct_constraints": [],  # Constraints that directly contain the variable
            "related_constraints": []  # Constraints on variables that appear with our target
        }

        # Regular expression to match the variable as a standalone identifier
        var_pattern = re.compile(r'(^|[^a-zA-Z0-9_])' + re.escape(variable_name) + r'([^a-zA-Z0-9_]|$)')

        # Track variables related to our target
        related_vars = set()

        # Keep track of all constraint strings we've seen to avoid duplicates
        seen_constraints = set()

        # First pass: find all direct constraints and collect related variables
        for c in self.solver.assertions():
            c_str = str(c)

            # Skip pi constant definitions
            if "pi ==" in c_str:
                continue

            # Check if this constraint directly involves our variable
            if var_pattern.search(c_str):
                formatted = self.format_constraint(c_str)

                # Only add if we haven't seen this formatted constraint before
                if formatted not in seen_constraints:
                    result["direct_constraints"].append(formatted)
                    seen_constraints.add(formatted)

                # Find variables in this constraint using different variable patterns
                for var_prefix in ["angle_", "length_", "arc_"]:
                    var_matches = re.findall(r'(' + var_prefix + r'\w+)', c_str)
                    for var_match in var_matches:
                        related_vars.add(var_match)

        # Second pass: find all constraints on related variables
        for c in self.solver.assertions():
            c_str = str(c)

            # Skip pi constants
            if "pi ==" in c_str:
                continue

            # Format constraint first to compare against seen_constraints
            formatted = self.format_constraint(c_str)

            # Skip if we've already seen this constraint
            if formatted in seen_constraints:
                continue

            # Check if any related variable appears in this constraint
            for var in related_vars:
                if var in c_str:
                    # Add to related constraints and mark as seen
                    result["related_constraints"].append(formatted)
                    seen_constraints.add(formatted)
                    break

        # Limit the number of constraints returned
        if max_constraints > 0:
            result["direct_constraints"] = result["direct_constraints"][:max_constraints // 2]
            result["related_constraints"] = result["related_constraints"][:max_constraints // 2]

        return result

    def add_all_side_mirror_ratio_constraints(self, tri1: str, tri2: str):
        """For mirror similar triangles, add side‐ratio constraints for each corresponding side.
        (This is analogous to add_all_side_ratios_for_similar_triangles.)"""

        def get_triangle_vertices(triangle_name: str) -> list:
            return list(triangle_name)

        verts1 = get_triangle_vertices(tri1)
        verts2 = get_triangle_vertices(tri2)
        norm_tris = self.normalize_similar_triangles(tri1, tri2)
        if not norm_tris:
            return
        if norm_tris in self.added_mirror_ratio_constraints:
            return
        if norm_tris not in self.mirror_triangle_ratios:
            var_name = f"ratio_mirror_{norm_tris[0]}_{norm_tris[1]}"
            self.mirror_triangle_ratios[norm_tris] = Real(var_name)
        ratio = self.mirror_triangle_ratios[norm_tris]
        for i in range(3):
            j = (i + 1) % 3
            p1a, p1b = verts1[i], verts1[j]
            p2a, p2b = verts2[i], verts2[j]
            side1_var = self.add_length(p1a, p1b)
            side2_var = self.add_length(p2a, p2b)
            self.solver.add(side1_var == side2_var * ratio)
        self.added_mirror_ratio_constraints.add(norm_tris)
        print(f"Added mirror similar side ratio constraints for triangles {tri1} and {tri2}.")

    def normalize_triangle(self, triangle: str) -> str:
        """Return the lexicographically smallest rotation of a triangle's name."""
        if len(triangle) != 3:
            return triangle
        rotations = [triangle[i:] + triangle[:i] for i in range(3)]
        return min(rotations)

    def are_triangles_similar(self, tri1: str, tri2: str) -> bool:
        # Use mirror–similar canonicalization for the purpose of mirror similarity
        canonical = self.canonicalize_mirror_triangle_pair(tri1, tri2)
        return canonical in self.similar_triangles or (canonical[1], canonical[0]) in self.similar_triangles

    def canonicalize_triangle_pair(self, tri1: str, tri2: str) -> Tuple[str, str]:
        """
        Given two triangles (each represented by a 3‐letter string),
        compute a canonical key that is invariant under (a) cyclic rotations (applied in lock‐step)
        and (b) switching the order of the triangles.

        For each rotation index i (0, 1, 2), we compute:
            r1 = tri1 rotated by i, and r2 = tri2 rotated by i.
        Then we consider both (r1, r2) and (r2, r1) (to be order–invariant)
        and choose the lexicographically smallest pair. Finally, we pick the smallest candidate
        among the three rotations.
        """
        if len(tri1) != 3 or len(tri2) != 3:
            raise ValueError("Each triangle must have exactly 3 vertices.")

        candidates = []
        for i in range(3):
            r1 = tri1[i:] + tri1[:i]
            r2 = tri2[i:] + tri2[:i]
            # Preserve the lock‐step rotation by first forming the candidate (r1, r2),
            # but then to get order invariance, compare with the swapped order.
            candidate = min((r1, r2), (r2, r1))
            candidates.append(candidate)

        return min(candidates)

    def canonicalize_triangle_pair(self, tri1: str, tri2: str) -> Tuple[str, str]:
        """
        Given two triangles (each represented by a 3‐letter string),
        compute a canonical key that is invariant under (a) cyclic rotations (applied in lock‐step)
        and (b) switching the order of the triangles.

        For each rotation index i (0, 1, 2), we compute:
            r1 = tri1 rotated by i, and r2 = tri2 rotated by i.
        Then we consider both (r1, r2) and (r2, r1) (to be order–invariant)
        and choose the lexicographically smallest pair. Finally, we pick the smallest candidate
        among the three rotations.
        """
        if len(tri1) != 3 or len(tri2) != 3:
            raise ValueError("Each triangle must have exactly 3 vertices.")

        candidates = []
        for i in range(3):
            r1 = tri1[i:] + tri1[:i]
            r2 = tri2[i:] + tri2[:i]
            # Preserve the lock‐step rotation by first forming the candidate (r1, r2),
            # but then to get order invariance, compare with the swapped order.
            candidate = min((r1, r2), (r2, r1))
            candidates.append(candidate)

        return min(candidates)

    def canonicalize_triangle_pair(self, tri1: str, tri2: str) -> Tuple[str, str]:
        """
        Given two triangles (each represented by a 3‐letter string),
        compute a canonical key that is invariant under (a) cyclic rotations (applied in lock‐step)
        and (b) switching the order of the triangles.

        For each rotation index i (0, 1, 2), we compute:
            r1 = tri1 rotated by i, and r2 = tri2 rotated by i.
        Then we consider both (r1, r2) and (r2, r1) (to be order–invariant)
        and choose the lexicographically smallest pair. Finally, we pick the smallest candidate
        among the three rotations.
        """
        if len(tri1) != 3 or len(tri2) != 3:
            raise ValueError("Each triangle must have exactly 3 vertices.")

        candidates = []
        for i in range(3):
            r1 = tri1[i:] + tri1[:i]
            r2 = tri2[i:] + tri2[:i]
            # Preserve the lock‐step rotation by first forming the candidate (r1, r2),
            # but then to get order invariance, compare with the swapped order.
            candidate = min((r1, r2), (r2, r1))
            candidates.append(candidate)

        return min(candidates)

    def add_similar_triangles(self, tri1: str, tri2: str):
        """
        Record that two triangles are similar and create their ratio variable.
        This function uses a canonical key obtained from cyclic rotations so that
        the pair (tri1, tri2) is uniquely identified regardless of rotation or order.

        Additionally attempts to compute the ratio value when sufficient constraints exist.
        """
        # Get the canonical pair from our helper.
        canonical_pair = self.canonicalize_mirror_triangle_pair(tri1, tri2)

        # Record the similarity using the canonical pair.
        if canonical_pair not in self.similar_triangles:
            self.similar_triangles.append(canonical_pair)
            print(f"Recorded similarity: triangles {tri1} and {tri2} (canonical: {canonical_pair})")

        # Create a ratio variable if it does not already exist.
        if canonical_pair not in self.triangle_ratios:
            var_name = f"ratio_{canonical_pair[0]}_{canonical_pair[1]}"
            self.triangle_ratios[canonical_pair] = Real(var_name)
            print(f"Created ratio variable: {var_name}")

        ratio_var = self.triangle_ratios[canonical_pair]

        # Try to compute the ratio automatically if solver is satisfiable
        if self.solver.check() == sat:
            model = self.solver.model()

            # Get the vertices of both triangles in their original order
            verts1 = list(tri1)
            verts2 = list(tri2)

            # Check if we can determine the ratio from any pair of corresponding sides
            ratio_determined = False
            attempted_pairs = []

            # Check all three pairs of corresponding sides
            for i in range(3):
                p1a, p1b = verts1[i], verts1[(i + 1) % 3]
                p2a, p2b = verts2[i], verts2[(i + 1) % 3]

                # Form the sides
                side1 = p1a + p1b
                side2 = p2a + p2b

                # Get the length variables
                len1_var = self.add_length(side1[0], side1[1])
                len2_var = self.add_length(side2[0], side2[1])

                attempted_pairs.append((side1, side2))

                # Check if both sides have unique values in the current model
                try:
                    # Create temporary solvers to check uniqueness
                    temp_solver1 = Solver()
                    for c in self.solver.assertions():
                        temp_solver1.add(c)

                    # Get current values
                    len1_val = float(model.eval(len1_var).as_decimal(10).rstrip('?'))
                    len2_val = float(model.eval(len2_var).as_decimal(10).rstrip('?'))

                    # Check uniqueness by trying to find different values
                    epsilon = 1e-8
                    temp_solver1.add(Or(
                        len1_var < len1_val - epsilon,
                        len1_var > len1_val + epsilon
                    ))

                    temp_solver2 = Solver()
                    for c in self.solver.assertions():
                        temp_solver2.add(c)

                    temp_solver2.add(Or(
                        len2_var < len2_val - epsilon,
                        len2_var > len2_val + epsilon
                    ))

                    # If both sides have unique values and second side is non-zero
                    if temp_solver1.check() == unsat and temp_solver2.check() == unsat and len2_val > epsilon:
                        computed_ratio = len1_val / len2_val

                        # Check if this ratio is consistent with existing constraints
                        temp_solver3 = Solver()
                        for c in self.solver.assertions():
                            temp_solver3.add(c)

                        # Try adding the computed ratio
                        temp_solver3.add(ratio_var == computed_ratio)

                        if temp_solver3.check() == sat:
                            # This ratio is consistent, so add it as a constraint
                            self.solver.add(ratio_var == computed_ratio)
                            print(f"✓ Automatically determined similarity ratio: {computed_ratio:.4f}")
                            print(f"  Based on sides: {side1}/{side2} = {len1_val:.4f}/{len2_val:.4f}")
                            ratio_determined = True
                            break
                        else:
                            print(
                                f"× Computed ratio {computed_ratio:.4f} from {side1}/{side2} inconsistent with existing constraints")
                except Exception as e:
                    # Just log and continue - don't disrupt the existing functionality
                    print(f"! Error checking side pair {side1}/{side2}: {str(e)}")

            if not ratio_determined:
                # Also try checking if ratio_var itself is uniquely determined
                try:
                    ratio_val = float(model.eval(ratio_var).as_decimal(10).rstrip('?'))

                    # Check if the ratio is uniquely determined
                    temp_solver = Solver()
                    for c in self.solver.assertions():
                        temp_solver.add(c)

                    epsilon = 1e-8
                    temp_solver.add(Or(
                        ratio_var < ratio_val - epsilon,
                        ratio_var > ratio_val + epsilon
                    ))

                    if temp_solver.check() == unsat:
                        # The ratio is already uniquely determined by existing constraints
                        print(f"✓ Similarity ratio already constrained to: {ratio_val:.4f}")
                        ratio_determined = True
                    else:
                        # To help with debugging, get an alternative value
                        alt_model = temp_solver.model()
                        alt_ratio = float(alt_model.eval(ratio_var).as_decimal(10).rstrip('?'))
                        print(f"! Similarity ratio not uniquely determined: could be {ratio_val} or {alt_ratio}")
                        print(f"  Attempted side pairs: {', '.join([f'{s1}/{s2}' for s1, s2 in attempted_pairs])}")
                except Exception as e:
                    print(f"! Error checking ratio uniqueness: {str(e)}")
        else:
            print("! Note: Cannot compute similarity ratio - solver is unsatisfiable")

        # Add the side ratio constraints for all corresponding sides (for backward compatibility)
        self.add_all_side_ratios_for_similar_triangles(tri1, tri2)

        # Also try to create non-degeneracy constraints for the triangles
        try:
            # Add a constraint that the ratio is positive (prevents zero-sized solutions)
            self.solver.add(ratio_var > 0)

            # Add constraints that all sides have positive length
            for tri in [tri1, tri2]:
                for i in range(3):
                    p1 = tri[i]
                    p2 = tri[(i + 1) % 3]
                    side_var = self.add_length(p1, p2)
                    # Use a small positive value instead of 0 to prevent near-zero solutions
                    self.solver.add(side_var > 0.001)
        except Exception as e:
            # Just log, don't disrupt existing functionality
            print(f"! Error adding non-degeneracy constraints: {str(e)}")

        return ratio_var  # Return the ratio variable for convenience

    def calculate_perimeter(self, triangle: str) -> Optional[Real]:
        """Calculate perimeter of a triangle"""
        if len(triangle) != 3:
            return None

        sides = []
        for i in range(3):
            p1 = triangle[i]
            p2 = triangle[(i + 1) % 3]
            length_var = self.add_length(p1, p2)
            sides.append(length_var)

        return sum(sides)

    def normalize_line_name(self, line_points: str) -> str:
        """Normalize line name (AB and BA are same line)"""
        if len(line_points) != 2:
            return line_points
        return min(line_points, line_points[::-1])

    def add_right_triangle(self, points: str):
        """Add a right triangle with 90° angle"""
        if len(points) != 3:
            return

        # Add the triangle to proven right triangles
        triangle = self.normalize_triangle(points)
        self.right_triangles.add(triangle)

        # Add 90° angle constraint
        angle_var = self.add_angle(points[0], points[1], points[2])

    def normalize_similar_triangles(self, tri1: str, tri2: str) -> Optional[Tuple[str, str]]:
        if len(tri1) != 3 or len(tri2) != 3:
            return None
        normalized = None
        for i in range(3):
            rot1 = tri1[i:] + tri1[:i]
            rot2 = tri2[i:] + tri2[:i]
            if normalized is None or (rot1, rot2) < normalized:
                normalized = (rot1, rot2)
        return normalized

    def normalize_arc(self, arc_str: str) -> str:
        """
        Normalize an arc name. For an arc given by three letters,
        the first character (the center) is kept in place,
        and the remaining two letters (the endpoints) are sorted alphabetically.
        For example, both "OMB" and "OBM" become "OBM".
        """
        if len(arc_str) != 3:
            return arc_str
        center = arc_str[0]
        endpoints = sorted([arc_str[1], arc_str[2]])
        return center + ''.join(endpoints)

    def normalize_angle_name(self, angle_points: str) -> str:
        """Normalize angle name (ABC and CBA are same angle, but ACB is different)"""
        if len(angle_points) != 3:
            return angle_points

        p1, vertex, p2 = angle_points[0], angle_points[1], angle_points[2]
        # Consider both orientations (DAB and BAD are the same)
        option1 = f"{p1}{vertex}{p2}"
        option2 = f"{p2}{vertex}{p1}"
        # Return the lexicographically smaller option
        return min(option1, option2)

    def normalize_collinear_points(self, points: str) -> str:
        """Normalize collinear points (ABC and CBA are same, but BCA is different)"""
        # Consider both forward and reversed order
        option1 = points
        option2 = points[::-1]
        # Return the lexicographically smaller option
        return min(option1, option2)

    def normalize_parallelogram(self, points: str) -> Set[str]:
        """Get all valid cyclic variations of parallelogram name
        ABCD becomes {ABCD, BCDA, CDAB, DABC} but not DCBA etc."""
        if len(points) != 4:
            return {points}

        variations = set()
        for i in range(4):
            # Add cyclic variation
            variation = points[i:] + points[:i]
            variations.add(variation)
        return variations

    def add_algebraic_arc(self, arc_name: str, expression: str):
        """Add an arc measure constraint that can be numeric or an algebraic expression."""
        print(f"\nAdding algebraic arc constraint: {arc_name} = {expression}")
        # Try to parse as a numeric value first.
        try:
            value = float(expression)
            print(f"Adding numeric value for arc {arc_name}: {value}")
            arc_var = self.add_arc(arc_name)
            self.solver.add(arc_var == value)
            return
        except ValueError:
            pass
        # If not purely numeric, extract any variables and create them if necessary.
        variables = self.extract_variables(expression)
        for var in variables:
            if var not in self.variables:
                self.variables[var] = Real(var)
                print(f"Created new variable for algebraic arc: {var}")
        arc_var = self.add_arc(arc_name)
        expr = self.parse_algebraic_expression(expression)
        self.solver.add(arc_var == expr)

    def add_arc(self, arc_str: str) -> Real:
        """
        Return the Z3 variable for the measure of the arc given by arc_str.
        The arc is normalized so that its first letter (the center) is fixed
        and the other two letters are sorted. We then constrain the arc measure
        to be between 0 and 360 (you can adjust the range as needed).
        """
        normalized = self.normalize_arc(arc_str)
        arc_name = f"arc_{normalized}"
        if arc_name not in self.arcs:
            self.arcs[arc_name] = Real(arc_name)
            self.solver.add(self.arcs[arc_name] >= 0, self.arcs[arc_name] <= 360)
            print(f"Created arc variable: {arc_name}")
        return self.arcs[arc_name]

    def add_collinear_fact(self, points: List[str]):
        """Add collinear points fact with supplementary angle relationships"""
        if len(points) < 3:
            return

        # Join points to string and normalize
        points_str = ''.join(points)
        normalized = self.normalize_collinear_points(points_str)
        points = list(normalized)  # Convert back to list

        # Also create reversed points
        reversed_points = points[::-1]

        # Process both orders
        for point_order in [points, reversed_points]:
            # For each three consecutive points
            for i in range(len(point_order) - 2):
                p1, v, p2 = point_order[i:i + 3]

                # Add points if they don't exist
                for p in [p1, v, p2]:
                    if p not in self.points:
                        self.add_point(p)

                # Add straight angle constraint (180°) - use normalized angle
                straight_angle = self.normalize_angle_name(p1 + v + p2)
                angle_var = self.add_angle(straight_angle[0], straight_angle[1], straight_angle[2])

                # Any other point forms supplementary angles with this line
                for q in self.points:
                    if q not in [p1, v, p2]:
                        # Create and normalize both angles
                        angle1_name = self.normalize_angle_name(p1 + v + q)
                        angle2_name = self.normalize_angle_name(q + v + p2)

                        # Add the angles to solver using normalized names
                        angle1_var = self.add_angle(angle1_name[0], angle1_name[1], angle1_name[2])
                        angle2_var = self.add_angle(angle2_name[0], angle2_name[1], angle2_name[2])

                        # These angles must be supplementary
                        # Each angle must be between 0° and 180°


            # Process endpoints for this order
            if len(point_order) >= 3:
                # Process each endpoint of the collinear set
                for endpoint in (point_order[0], point_order[-1]):
                    # Choose the neighbor that is adjacent to the endpoint
                    ref = point_order[1] if endpoint == point_order[0] else point_order[-2]

                    # For every other point in the collinear set
                    for other in point_order:
                        if other == endpoint or other == ref:
                            continue

                        # For every external point Q
                        for q in self.points:
                            if q not in point_order:
                                # Construct the angles
                                angle_ref = self.normalize_angle_name(f"{ref}{endpoint}{q}")
                                angle_other = self.normalize_angle_name(f"{other}{endpoint}{q}")

                                # Add the equality constraint
                                a_ref_var = self.add_angle(angle_ref[0], angle_ref[1], angle_ref[2])
                                a_other_var = self.add_angle(angle_other[0], angle_other[1], angle_other[2])
                                self.solver.add(a_ref_var == a_other_var)
                                print(f"Derived from collinearity: {angle_ref} = {angle_other}")

    def parse_algebraic_expression(self, expr: str) -> Real:
        """Convert string expression to Z3 expression using any variables"""
        expr = expr.strip()
        try:
            # Handle pure variable case
            if expr in self.variables:
                return self.variables[expr]

            # Try to convert to float first with math functions
            try:
                import math
                eval_env = {"sqrt": math.sqrt, "pi": math.pi}
                return float(eval(expr, {"__builtins__": {}}, eval_env))
            except Exception:
                pass

            # Check for sqrt pattern
            sqrt_match = re.search(r'sqrt\((.+?)\)', expr)
            if sqrt_match:
                inner_expr = sqrt_match.group(1)
                inner_value = self.parse_algebraic_expression(inner_expr)
                # Use z3's power function for square root
                from z3 import Pow
                return Pow(inner_value, 0.5)

            # Handle arithmetic operations
            if '+' in expr:
                left, right = expr.rsplit('+', 1)
                return self.parse_algebraic_expression(left) + self.parse_algebraic_expression(right)
            elif '-' in expr and not expr.startswith('-'):
                left, right = expr.rsplit('-', 1)
                return self.parse_algebraic_expression(left) - self.parse_algebraic_expression(right)
            elif expr.startswith('-'):
                return -self.parse_algebraic_expression(expr[1:])
            elif '/' in expr:
                num, denom = expr.split('/')
                return self.parse_algebraic_expression(num) / self.parse_algebraic_expression(denom)
            elif '*' in expr:
                left, right = expr.split('*', 1)  # Changed to split on first '*'
                return self.parse_algebraic_expression(left) * self.parse_algebraic_expression(right)

            # If we get here, check if any variables are in the expression
            for var_name, var in self.variables.items():
                if var_name in expr:
                    return self.variables[var_name]

            raise ValueError(f"Cannot parse expression: {expr}")

        except Exception as e:
            print(f"Error parsing expression '{expr}': {str(e)}")
            raise

    def collect_related_facts_for_line(self, line_points):
        """Collect only facts where at least one point is part of the line"""
        related_facts = {}
        line_points_set = set(line_points)

        # 1. Points in the line
        related_facts["Points"] = line_points

        # 2. Collect lines containing at least one point from our line
        related_lines = []
        for line_name, line_var in self.lengths.items():
            # Extract points from line name (typically in format "length_AB")
            line_points_str = line_name.split('_')[1] if '_' in line_name else line_name
            if any(p in line_points_set for p in line_points_str) and line_points_str != ''.join(line_points):
                related_lines.append(f"Line {line_points_str}")
        related_facts["Related Lines"] = related_lines

        # 3. Collect triangles containing both points of our line
        related_triangles = []
        for polygon in self.polygons:
            if len(polygon) == 3 and all(p in polygon for p in line_points):
                properties = []
                if polygon in self.right_triangles:
                    properties.append("right")
                if hasattr(self, 'isosceles_triangles') and polygon in self.isosceles_triangles:
                    properties.append("isosceles")
                if properties:
                    related_triangles.append(f"Triangle {polygon} ({', '.join(properties)})")
                else:
                    related_triangles.append(f"Triangle {polygon}")
        related_facts["Triangles Containing This Line"] = related_triangles

        # 4. Collect quadrilaterals containing both points of our line
        related_quads = []
        for polygon in self.polygons:
            if len(polygon) == 4 and all(p in polygon for p in line_points):
                properties = []
                if polygon in self.parallelograms:
                    properties.append("parallelogram")
                if hasattr(self, 'rectangles') and polygon in self.rectangles:
                    properties.append("rectangle")
                if hasattr(self, 'squares') and polygon in self.squares:
                    properties.append("square")
                if properties:
                    related_quads.append(f"Quadrilateral {polygon} ({', '.join(properties)})")
                else:
                    related_quads.append(f"Quadrilateral {polygon}")
        related_facts["Quadrilaterals Containing This Line"] = related_quads

        # 5. Collect parallel line pairs involving this line
        related_parallel = []
        line_str = ''.join(line_points)
        for pair in self.parallel_pairs:
            if line_str in [pair[0], pair[1], pair[0][::-1], pair[1][::-1]]:
                other_line = pair[1] if (pair[0] == line_str or pair[0][::-1] == line_str) else pair[0]
                related_parallel.append(f"Parallel to {other_line}")
        related_facts["Parallel Relationships"] = related_parallel

        # 6. Collect perpendicular line pairs involving this line
        related_perp = []
        for pair in self.perpendicular_pairs:
            if line_str in [pair[0], pair[1], pair[0][::-1], pair[1][::-1]]:
                other_line = pair[1] if (pair[0] == line_str or pair[0][::-1] == line_str) else pair[0]
                related_perp.append(f"Perpendicular to {other_line}")
        related_facts["Perpendicular Relationships"] = related_perp

        # 7. Check if this line is a radius, diameter, or chord of a circle
        circle_relationships = []
        for circle, center in self.circle_centers.items():
            if center in line_points and any(p != center and p in line_points for p in line_points):
                circle_relationships.append(f"Radius of circle {circle}")

        for diam_tuple in self.is_diameter_of_circle:
            diam_line, circle = diam_tuple
            if diam_line == line_str or diam_line[::-1] == line_str:
                circle_relationships.append(f"Diameter of circle {circle}")

        related_facts["Circle Relationships"] = circle_relationships

        # Remove empty categories
        return {k: v for k, v in related_facts.items() if v}

    def generate_premise_error_feedback(self, theorem_name, args, premise, conclusions, error):
        """Generate user-friendly feedback for premise errors with complete theorem call information"""

        # Format the complete theorem call information
        args_str = ",".join(args)

        # Custom error message for premise errors
        error_message = TRIED_THEOREM.format(theorem_name, args_str, premise, str(conclusions))
        error_message += MISSING_PREMISE.format(error.message)

        # Include details if available and not empty
        if error.details and not (
                "Available parallel pairs: set()" in error.details or
                "Known parallel pairs: set()" in error.details or
                "Available" in error.details and "set()" in error.details or
                "Known" in error.details and "set()" in error.details
        ):
            error_message += DETAILS_PREFIX.format(error.details)

        # Get geometric facts
        geometric_data = self.gather_relevant_geometric_data()

        # Check if we have goal information
        goal_token = getattr(self, 'goal_token', None)
        goal_type = getattr(self, 'goal_type', None)

        # Find relevant theorems based on the goal
        related_theorems = []
        if goal_token:
            for theorem_info in self.theorem_sequence:
                is_related = False

                # For simple token goals (length, angle, etc.)
                if isinstance(goal_token, str) and len(goal_token) <= 5:  # Simple goal tokens
                    # Check if the token is mentioned directly
                    if goal_token in ' '.join(theorem_info["conclusions"]):
                        is_related = True
                    elif goal_token in theorem_info["premise"]:
                        is_related = True
                    elif any(goal_token in arg for arg in theorem_info["args"]):
                        is_related = True

                # For compound tokens (like "AB+CD" or "AB/CD")
                elif isinstance(goal_token, str) and '+' in goal_token:
                    parts = goal_token.split('+')
                    if any(part in ' '.join(theorem_info["conclusions"]) for part in parts):
                        is_related = True
                elif isinstance(goal_token, str) and '/' in goal_token:
                    parts = goal_token.split('/')
                    if any(part in ' '.join(theorem_info["conclusions"]) for part in parts):
                        is_related = True

                # For general expressions, check for patterns
                elif goal_type == "general":
                    # Try looking for known patterns in the expression
                    if 'LengthOfLine' in goal_token:
                        pattern = r'LengthOfLine\((\w+)\)'
                        matches = re.findall(pattern, goal_token)
                        if any(match in ' '.join(theorem_info["conclusions"]) for match in matches):
                            is_related = True
                    elif 'MeasureOfAngle' in goal_token:
                        pattern = r'MeasureOfAngle\((\w+)\)'
                        matches = re.findall(pattern, goal_token)
                        if any(match in ' '.join(theorem_info["conclusions"]) for match in matches):
                            is_related = True

                if is_related:
                    related_theorems.append({
                        "step": theorem_info["step_number"],
                        "theorem": theorem_info["theorem_name"],
                        "args": theorem_info["args"],
                        "conclusion": ", ".join(theorem_info["conclusions"])
                    })

        # Find relevant constraints based on the goal
        relevant_constraints = []
        if goal_token and goal_type:
            var_names = []

            # Determine variable names based on goal type
            if goal_type == "length":
                var_names.append(f"length_{self.normalize_line_name(goal_token)}")
            elif goal_type == "angle":
                var_names.append(f"angle_{self.normalize_angle_name(goal_token)}")
            elif goal_type == "arc_measure":
                var_names.append(f"arc_{self.normalize_arc(goal_token)}")
            elif goal_type == "arc_length":
                var_names.append(f"lengthArc_{self.normalize_arc(goal_token)}")
                var_names.append(f"arc_{self.normalize_arc(goal_token)}")
            elif goal_type == "radius":
                var_names.append(f"radius_{goal_token}")
            elif goal_type == "cosine":
                var_names.append(f"cos_{goal_token}")
                var_names.append(f"angle_{self.normalize_angle_name(goal_token)}")
            elif goal_type == "sine":
                var_names.append(f"sin_{goal_token}")
                var_names.append(f"angle_{self.normalize_angle_name(goal_token)}")
            elif goal_type == "sum":
                tokens = goal_token.split('+')
                for token in tokens:
                    var_names.append(f"length_{self.normalize_line_name(token)}")
            elif goal_type == "ratio":
                tokens = goal_token.split('/')
                for token in tokens:
                    var_names.append(f"length_{self.normalize_line_name(token)}")
            elif goal_type == "perimeter":
                var_names.append(f"perimeter_{goal_token}")
            elif goal_type == "quad_area":
                var_names.append(f"AreaOfQuadrilateral_{goal_token}")
            elif goal_type == "triangle_area":
                normalized = ''.join(sorted(goal_token))
                var_names.append(f"areaTriangle_{normalized}")
            elif goal_type == "general":
                # For general goals, try to find any part that looks like a variable
                variables = self.extract_variables(goal_token)
                for var in variables:
                    var_names.append(var)

            # Filter constraints that mention these variables
            for c in self.solver.assertions():
                c_str = str(c)
                if "pi ==" not in c_str:  # Skip pi constant definition
                    for var_name in var_names:
                        if var_name in c_str:
                            formatted = self.format_constraint(c_str)
                            if formatted not in relevant_constraints:
                                relevant_constraints.append(formatted)
                            break

        # Use the common feedback report function with customized error message
        return self.create_feedback_report(
            goal_type="premise_error",
            goal_token=theorem_name,
            model_answer=None,
            status="premise_violation",
            error_message=error_message,
            geometric_data=geometric_data,
            related_theorems=related_theorems,
            relevant_constraints=relevant_constraints
        )

    def find_related_theorems_for_line(self, line_name, line_points):
        """Find theorems that directly relate to the line"""
        related_theorems = []
        line_points_set = set(line_points)

        for theorem_info in self.theorem_sequence:
            is_related = False

            # Check if line is directly mentioned in conclusions
            for conclusion in theorem_info["conclusions"]:
                if f"LengthOfLine({line_name})" in conclusion:
                    is_related = True
                    break

                # Look for normalized versions
                norm_line = self.normalize_line_name(line_name)
                if f"LengthOfLine({norm_line})" in conclusion:
                    is_related = True
                    break

            # Check if mentioned in the premise
            if line_name in theorem_info["premise"]:
                is_related = True

            # Check if mentioned in args
            if any(line_name in arg for arg in theorem_info["args"]):
                is_related = True

            # Check if any of the points is mentioned in a side ratio or similar triangle context
            if any("RatioOfSimilarTriangle" in c and any(p in c for p in line_points) for c in
                   theorem_info["conclusions"]):
                is_related = True

            if is_related:
                related_theorems.append({
                    "step": theorem_info["step_number"],
                    "theorem": theorem_info["theorem_name"],
                    "args": theorem_info["args"],
                    "conclusion": ", ".join(theorem_info["conclusions"])
                })

        return related_theorems

    def add_algebraic_angle(self, angle_name: str, expression: str):
        """Add an angle with an algebraic expression"""
        print(f"\nAdding algebraic angle constraint: {angle_name} = {expression}")

        # Try to parse as numeric first
        try:
            value = float(expression)
            print(f"Adding numeric value: {angle_name} = {value}")
            normalized = self.normalize_angle_name(angle_name)

            # Add to both known values and constraints
            angle_var = self.add_angle(normalized[0], normalized[1], normalized[2])
            self.solver.add(angle_var == value)
            # Store the expression even though it's numeric
            print(f"Stored numeric value: {normalized} = {value}")
            return
        except ValueError:
            # Not a numeric value, handle as algebraic expression
            pass

        # Find variables in expression
        variables = self.extract_variables(expression)

        # Create Z3 variables for algebraic expression
        for var in variables:
            if var not in self.variables:
                self.variables[var] = Real(var)
                print(f"Created new variable: {var}")

        angle_var = self.add_angle(angle_name[0], angle_name[1], angle_name[2])
        expr = self.parse_algebraic_expression(expression)
        self.solver.add(angle_var == expr)

        # Store original expression
        normalized = self.normalize_angle_name(angle_name)

    def apply_triangle_area_sine(self):
        """
        For every stored triangle_area_sine relationship,
        if the solver can determine numeric values for both side lengths and the included angle,
        then compute the area and add a constraint fixing the area variable.
        """
        import math
        for rel in self.proven_area_relationships:
            if rel[0] == "triangle_area_sine":
                # rel is assumed to have the form:
                # ("triangle_area_sine", triangle_name, side1, side2, angle, factor_str)
                _, tri_name, s1, s2, ang, factor_str = rel

                # Get the Z3 variables for the two side lengths and the angle.
                s1_var = self.add_length(s1[0], s1[1])
                s2_var = self.add_length(s2[0], s2[1])
                ang_var = self.add_angle(ang[0], ang[1], ang[2])

                # Query the solver for numeric values.
                if self.solver.check() == sat:
                    model = self.solver.model()
                    try:
                        # Evaluate the side and angle variables.
                        val_s1 = model.eval(s1_var)
                        val_s2 = model.eval(s2_var)
                        val_ang = model.eval(ang_var)
                        # Convert to float. (If the result ends with '?', remove it.)
                        s1_val = float(val_s1.as_decimal(10).rstrip('?'))
                        s2_val = float(val_s2.as_decimal(10).rstrip('?'))
                        ang_val = float(val_ang.as_decimal(10).rstrip('?'))
                    except Exception as e:
                        print("Could not convert model values to float:", e)
                        continue

                    try:
                        factor_val = float(eval(factor_str))
                    except Exception:
                        factor_val = 0.5

                    # Compute area numerically.
                    area_val = factor_val * s1_val * s2_val * math.sin(math.radians(ang_val))
                    # Create or get the triangle's area variable.
                    if tri_name not in self.triangle_areas:
                        self.triangle_areas[tri_name] = Real(f"areaTriangle_{tri_name}")
                        self.solver.add(self.triangle_areas[tri_name] >= 0)
                    self.solver.add(self.triangle_areas[tri_name] == area_val)
                    print(f"[apply_triangle_area_sine] Set AreaOfTriangle({tri_name}) = {area_val:.3f}")

    def triangle_angles(self, triangle: str) -> List[str]:
        """
        Returns the three canonical angle names (as strings) for the given triangle.
        For triangle "ADC", it returns the normalized versions of "DAC", "ADC", and "CDA".
        (Here the vertex is always the middle letter.)
        """
        angles = []
        # For each vertex index i in the triangle:
        for i in range(3):
            p_prev = triangle[(i - 1) % 3]
            vertex = triangle[i]
            p_next = triangle[(i + 1) % 3]
            angle_str = self.normalize_angle_name(p_prev + vertex + p_next)
            angles.append(angle_str)
        return angles

    def check_angle_equality(self, angle_str1: str, angle_str2: str) -> bool:
        """
        Returns True if, given the current constraints, the solver forces the angle variables
        corresponding to angle_str1 and angle_str2 to be equal.
        """
        # Get (or create) the angle variables.
        a1 = self.add_angle(angle_str1[0], angle_str1[1], angle_str1[2])
        a2 = self.add_angle(angle_str2[0], angle_str2[1], angle_str2[2])
        # Create a temporary solver that includes all current constraints.
        temp_solver = Solver()
        for c in self.solver.assertions():
            temp_solver.add(c)
        # Now add the extra constraint that a1 != a2.
        temp_solver.add(a1 != a2)
        # If that makes the system unsatisfiable, then a1 == a2 is forced.
        return temp_solver.check() == unsat

    def impose_square_constraints(self, shape_name: str):
        """
        Given a 4-letter shape name (like 'ABCD' or 'HEFG'),
        automatically impose the constraints for a square:
          - All 4 sides equal
          - All 4 interior angles are 90 degrees
        """
        # Make sure we have exactly 4 distinct letters
        if len(shape_name) != 4:
            return  # Skip if it's not 4 letters

        p1, p2, p3, p4 = shape_name[0], shape_name[1], shape_name[2], shape_name[3]

        # 1) Sides: AB=BC=CD=DA for shape ABCD
        side12 = self.add_length(p1, p2)
        side23 = self.add_length(p2, p3)
        side34 = self.add_length(p3, p4)
        side41 = self.add_length(p4, p1)
        # Impose equalities
        self.solver.add(side12 == side23)
        self.solver.add(side23 == side34)
        self.solver.add(side34 == side41)
        print(f"[Square {shape_name}] Imposed side equalities: {p1}{p2}={p2}{p3}={p3}{p4}={p4}{p1}")

        # 2) Angles: ABC=BCD=CDA=DAB=90
        # That means angle p1p2p3, angle p2p3p4, angle p3p4p1, angle p4p1p2 are each 90
        angle_123 = self.add_angle(p1, p2, p3)  # e.g. ABC
        angle_234 = self.add_angle(p2, p3, p4)  # e.g. BCD
        angle_341 = self.add_angle(p3, p4, p1)  # e.g. CDA
        angle_412 = self.add_angle(p4, p1, p2)  # e.g. DAB

        self.solver.add(angle_123 == 90)
        self.solver.add(angle_234 == 90)
        self.solver.add(angle_341 == 90)
        self.solver.add(angle_412 == 90)
        print(f"[Square {shape_name}] Imposed right angles at {p2}, {p3}, {p4}, {p1}")

    # Add this helper function to your GeometricTheorem class
    def evaluate_general_sub_expression(self, goal_expr, model):
        """Parse and evaluate a Sub() expression, including angle measures"""
        # Extract the two operands from Sub(expr1, expr2)
        inner = goal_expr[4:-1]  # Remove Sub( and )
        parts = inner.split(',')
        if len(parts) != 2:
            raise ValueError(f"Sub expression expected 2 parts, got: {len(parts)}")

        expr1_str = parts[0].strip()
        expr2_str = parts[1].strip()

        # Check for angle measure patterns
        angle1_match = re.match(r'MeasureOfAngle\((\w+)\)', expr1_str)
        angle2_match = re.match(r'MeasureOfAngle\((\w+)\)', expr2_str)

        if angle1_match and angle2_match:
            angle1_name = angle1_match.group(1)
            angle2_name = angle2_match.group(1)

            # Get angle variables
            angle1_var = self.add_angle(angle1_name[0], angle1_name[1], angle1_name[2])
            angle2_var = self.add_angle(angle2_name[0], angle2_name[1], angle2_name[2])

            # Evaluate each angle
            angle1_val = float(model.eval(angle1_var).as_decimal(10).rstrip('?'))
            angle2_val = float(model.eval(angle2_var).as_decimal(10).rstrip('?'))

            # Return the difference
            return angle1_val - angle2_val

        # Add other Sub() patterns as needed here
        # For example, you can add support for other types of measures

        # If no pattern matches, raise an error
        raise ValueError(f"Unsupported Sub expression format: {goal_expr}")

    def check_value_constraint(self, goal_var, model_answer, epsilon=1e-8):
        """
        Check if a variable matches an expected value with appropriate constraints.

        Returns: (success, value, status)
        - success: True if variable can only be the expected value
        - value: Current/alternative value (for reporting)
        - status: "unique", "incompatible", "multiple_values", or "unsatisfiable"
        """
        if self.solver.check() == sat:
            model = self.solver.model()

            # First check if constraints allow the expected value
            temp_solver1 = Solver()
            for c in self.solver.assertions():
                temp_solver1.add(c)

            # Add constraint that goal_var == expected (within epsilon)
            temp_solver1.add(And(goal_var >= model_answer - epsilon, goal_var <= model_answer + epsilon))

            if temp_solver1.check() != sat:
                # Get current value
                try:
                    verifier_expected_answer = float(model.eval(goal_var).as_decimal(10).rstrip('?'))
                    return False, verifier_expected_answer, "incompatible"
                except Exception as e:
                    return False, None, f"Error computing value: {str(e)}"

            # Now check if any other value is allowed
            temp_solver2 = Solver()
            for c in self.solver.assertions():
                temp_solver2.add(c)

            # Add constraint: goal_var != expected (outside epsilon range)
            temp_solver2.add(Or(goal_var < model_answer - epsilon, goal_var > model_answer + epsilon))

            if temp_solver2.check() == sat:
                try:
                    alt_model = temp_solver2.model()
                    verifier_expected_answer = float(alt_model.eval(goal_var).as_decimal(10).rstrip('?'))
                    return False, verifier_expected_answer, "multiple_values"
                except Exception as e:
                    return False, None, f"Error computing alternative value: {str(e)}"

            # If we get here, the constraints uniquely determine the value
            return True, model_answer, "unique"
        else:
            return False, None, "unsatisfiable"

    def evaluate_expression(self, expr, mapping):
        """Evaluate a general expression using the provided mapping."""
        # Add math functions and constants
        import math
        mapping["pi"] = math.pi
        mapping["sqrt"] = math.sqrt

        # Add helper functions
        def Sub(x, y):
            return x - y

        mapping["Sub"] = Sub

        # Evaluate the expression
        return eval(expr, mapping)

    def validate_theorem_premises(self, theorem_name: str, args: List[str], premise: str) -> Tuple[ bool, Optional[GeometricError]]:
        """Validate theorem premises and return appropriate error if validation fails"""

        # Helper function to return error and set the flag
        def return_error(error):
            self.found_tier_1_or_2_error = True
            return False, error

        if theorem_name == "adjacent_complementary_angle":
            version = args[0]
            if version == "1":
                if len(args) < 3:
                    return return_error(GeometricError(
                        tier=ErrorTier.TIER1_THEOREM_CALL_SYNTAX_VIOLATION,
                        message="Missing angle arguments",
                        details="adjacent_complementary_angle requires two angles"
                    ))

                # Check for collinear points in premise
                if "Collinear" in premise:
                    collinear_match = re.search(r'Collinear\((\w+)\)', premise)
                    if collinear_match:
                        points = collinear_match.group(1)  # e.g. "CDA"
                        # Normalize the points from premise
                        normalized_premise_points = self.normalize_collinear_points(points)

                        # Check if these normalized points exist in collinear_facts
                        collinear_found = False
                        for fact in self.collinear_facts:
                            # Try both original and reversed order
                            fact_forward = self.normalize_collinear_points(''.join(fact))
                            fact_reversed = self.normalize_collinear_points(''.join(fact[::-1]))

                            if normalized_premise_points in [fact_forward, fact_reversed]:
                                collinear_found = True
                                break

                        if not collinear_found:
                            return return_error(GeometricError(
                                tier=ErrorTier.TIER2_PREMISE_VIOLATION,
                                message=f"Points {points} are not proven collinear",
                                details=f"Known collinear facts: {self.collinear_facts}"
                            ))

                        # Verify the angles exist
                        angle1, angle2 = args[1], args[2]  # e.g. "CDB", "BDA"

                        # Check that both angles contain the shared point
                        shared_point = None
                        for p in angle1:
                            if p in angle2:
                                shared_point = p
                                break

                        if not shared_point:
                            return return_error(GeometricError(
                                tier=ErrorTier.TIER2_PREMISE_VIOLATION,
                                message=f"Angles {angle1} and {angle2} must share a vertex",
                                details="Required for adjacent complementary angles"
                            ))

                        # Check that the shared point is in the collinear set
                        if shared_point not in points:
                            return return_error(GeometricError(
                                tier=ErrorTier.TIER2_PREMISE_VIOLATION,
                                message=f"Shared point {shared_point} must be on the collinear line {points}",
                                details="Vertex must be on the collinear line"
                            ))

                        return True, None
                    else:
                        return return_error(GeometricError(
                            tier=ErrorTier.TIER2_PREMISE_VIOLATION,
                            message="Invalid collinear points format in premise"
                        ))
                else:
                    return return_error(GeometricError(
                        tier=ErrorTier.TIER2_PREMISE_VIOLATION,
                        message="Missing collinear points in premise",
                        details="adjacent_complementary_angle theorem requires collinear points"
                    ))
            else:
                return return_error(GeometricError(
                    tier=ErrorTier.TIER1_THEOREM_CALL_SYNTAX_VIOLATION,
                    message="these is no such version for the theorem",
                    details="these is no such version for the theorem adjacent_complementary_angle"
                ))
        elif theorem_name == "bisector_of_angle_property_line_ratio":
            version = args[0]
            if version == "1":
                if len(args) < 3:
                    return return_error(GeometricError(
                        tier=ErrorTier.TIER1_THEOREM_CALL_SYNTAX_VIOLATION,
                        message="Insufficient arguments for bisector_of_angle_property_line_ratio",
                        details="Expected: bisector_of_angle_property_line_ratio(1, bisector, angle)"
                    ))

                bisector = args[1].strip()  # e.g., "BD"
                angle = args[2].strip()  # e.g., "ABC"

                # Check for angle bisector fact in premise
                bisector_match = re.search(
                    r'IsBisectorOfAngle\(' + re.escape(bisector) + r',' + re.escape(angle) + r'\)', premise)
                if not bisector_match:
                    return return_error(GeometricError(
                        tier=ErrorTier.TIER2_PREMISE_VIOLATION,
                        message=f"Missing IsBisectorOfAngle({bisector},{angle}) in premise",
                        details="bisector_of_angle_property_line_ratio requires angle bisector fact"
                    ))

                # Check if angle bisector is stored in the system
                if hasattr(self, "angle_bisectors") and (bisector, angle) not in self.angle_bisectors:
                    return return_error(GeometricError(
                        tier=ErrorTier.TIER2_PREMISE_VIOLATION,
                        message=f"Angle bisector {bisector} for angle {angle} not established",
                        details=f"Known angle bisectors: {self.angle_bisectors}"
                    ))

                # Check for collinearity fact in premise
                collinear_match = re.search(r'Collinear\((\w+)\)', premise)
                if not collinear_match:
                    return return_error(GeometricError(
                        tier=ErrorTier.TIER2_PREMISE_VIOLATION,
                        message="Missing Collinear(...) fact in premise",
                        details="bisector_of_angle_property_line_ratio requires collinearity relationship"
                    ))

                collinear_points = collinear_match.group(1)

                # Check if this collinearity is stored in the system
                collinear_normalized = self.normalize_collinear_points(collinear_points)
                collinear_found = False
                for fact in self.collinear_facts:
                    fact_normalized = self.normalize_collinear_points(''.join(fact))
                    if fact_normalized == collinear_normalized:
                        collinear_found = True
                        break

                if not collinear_found:
                    return return_error(GeometricError(
                        tier=ErrorTier.TIER2_PREMISE_VIOLATION,
                        message=f"Collinearity {collinear_points} not established",
                        details=f"Known collinear facts: {[''.join(fact) for fact in self.collinear_facts]}"
                    ))

                # Verify that the geometric setup is correct for the theorem
                # The bisector must connect a vertex of the angle to a point on the opposite side
                # The collinear points must include the endpoint of the bisector and the other two points

                # The angle vertex is the middle letter of the angle
                vertex = angle[1]

                # The bisector should start at the vertex
                if bisector[0] != vertex:
                    return return_error(GeometricError(
                        tier=ErrorTier.TIER2_PREMISE_VIOLATION,
                        message=f"Bisector {bisector} doesn't start at angle vertex {vertex}",
                        details="The angle bisector must start at the angle's vertex"
                    ))

                # The collinear points should include the endpoint of the bisector
                # and the other two points of the triangle
                if bisector[1] not in collinear_points:
                    return return_error(GeometricError(
                        tier=ErrorTier.TIER2_PREMISE_VIOLATION,
                        message=f"Collinear points {collinear_points} don't include bisector endpoint {bisector[1]}",
                        details="The collinear points must include the endpoint of the bisector"
                    ))

                return True, None
            else:
                return return_error(GeometricError(
                    tier=ErrorTier.TIER1_THEOREM_CALL_SYNTAX_VIOLATION,
                    message="these is no such version for the theorem",
                    details="these is no such version for the theorem bisector_of_angle_property_line_ratio"
                ))
        elif theorem_name == "perpendicular_judgment_angle":
            version = args[0]
            if version == "1":
                if len(args) < 3:
                    return return_error(GeometricError(
                        tier=ErrorTier.TIER1_THEOREM_CALL_SYNTAX_VIOLATION,
                        message="Insufficient arguments for perpendicular_judgment_angle",
                        details="Expected: perpendicular_judgment_angle(1, line1, line2)"
                    ))

                line1, line2 = args[1].strip(), args[2].strip()

                # Extract the shared point between the lines
                shared_point = None
                for p in line1:
                    if p in line2:
                        shared_point = p
                        break

                if shared_point is None:
                    return return_error(GeometricError(
                        tier=ErrorTier.TIER2_PREMISE_VIOLATION,
                        message=f"Lines {line1} and {line2} do not share a common point",
                        details="perpendicular_judgment_angle requires lines to intersect at a point"
                    ))

                # Construct the expected angle
                other_point1 = next(p for p in line1 if p != shared_point)
                other_point2 = next(p for p in line2 if p != shared_point)
                expected_angle = other_point1 + shared_point + other_point2  # e.g., "EGD"

                # Check that the angle is defined in the premise
                angle_match = re.search(r'Angle\((\w+)\)', premise)
                if not angle_match:
                    return return_error(GeometricError(
                        tier=ErrorTier.TIER2_PREMISE_VIOLATION,
                        message="Missing angle definition in premise",
                        details="perpendicular_judgment_angle requires Angle(...) in premise"
                    ))

                premise_angle = angle_match.group(1)

                # Check that the angle in premise is the one formed by our lines
                # Note: We normalize both angles for comparison to handle different orderings
                normalized_premise_angle = self.normalize_angle_name(premise_angle)
                normalized_expected_angle = self.normalize_angle_name(expected_angle)

                if normalized_premise_angle != normalized_expected_angle:
                    return return_error(GeometricError(
                        tier=ErrorTier.TIER2_PREMISE_VIOLATION,
                        message=f"Premise angle {premise_angle} does not match the angle formed by lines {line1} and {line2}",
                        details=f"Expected angle {expected_angle} or equivalent"
                    ))

                # Check that the angle measure is specified as 90 degrees
                angle_measure_match = re.search(r'Equal\(MeasureOfAngle\(' + re.escape(premise_angle) + r'\),90\)',
                                                premise)
                if not angle_measure_match:
                    return return_error(GeometricError(
                        tier=ErrorTier.TIER2_PREMISE_VIOLATION,
                        message="Missing 90-degree angle specification in premise",
                        details=f"Need Equal(MeasureOfAngle({premise_angle}),90) in premise"
                    ))

                return True, None
            else:
                return return_error(GeometricError(
                    tier=ErrorTier.TIER1_THEOREM_CALL_SYNTAX_VIOLATION,
                    message="these is no such version for the theorem",
                    details="these is no such version for the theorem perpendicular_judgment_angle"
                ))

        elif theorem_name == "circle_property_angle_of_osculation":
            version = args[0]
            if version in {"1", "2"}:
                if len(args) < 3:
                    return return_error(GeometricError(
                        tier=ErrorTier.TIER1_THEOREM_CALL_SYNTAX_VIOLATION,
                        message="Insufficient arguments for circle_property_angle_of_osculation",
                        details=f"Expected: circle_property_angle_of_osculation({version}, arc, point)"
                    ))

                arc = args[1].strip()  # e.g., "OAB"
                tangent_point = args[2].strip()  # e.g., "P"

                # Check that the arc exists in premise
                arc_match = re.search(r'Arc\(' + re.escape(arc) + r'\)', premise)
                if not arc_match:
                    return return_error(GeometricError(
                        tier=ErrorTier.TIER2_PREMISE_VIOLATION,
                        message=f"Missing Arc({arc}) in premise",
                        details="circle_property_angle_of_osculation requires arc to be defined"
                    ))

                # Extract circle and points
                circle = arc[0]  # e.g., "O"
                point_a = arc[1]  # e.g., "A"
                point_b = arc[2]  # e.g., "B"

                # Determine which point is the tangent point based on version
                tangent_to_point = point_a if version == "1" else point_b

                # Check for angle in premise
                expected_angle = ""
                if version == "1":
                    expected_angle = point_b + point_a + tangent_point  # "BAP"
                else:  # version == "2"
                    expected_angle = tangent_point + point_b + point_a  # "PBA"



                # Check for tangent relationship
                expected_tangent = tangent_point + tangent_to_point  # e.g., "PA" or "PB"
                tangent_match = re.search(
                    r'IsTangentOfCircle\(' + re.escape(expected_tangent) + r',' + re.escape(circle) + r'\)', premise)
                if not tangent_match:
                    return return_error(GeometricError(
                        tier=ErrorTier.TIER2_PREMISE_VIOLATION,
                        message=f"Missing IsTangentOfCircle({expected_tangent},{circle}) in premise",
                        details=f"Version {version} requires line from {tangent_point} to be tangent at point {tangent_to_point}"
                    ))

                # Verify tangent fact exists in system
                if not hasattr(self, "tangent_facts") or (expected_tangent, circle) not in self.tangent_facts:
                    return return_error(GeometricError(
                        tier=ErrorTier.TIER2_PREMISE_VIOLATION,
                        message=f"Tangent fact IsTangentOfCircle({expected_tangent},{circle}) not established",
                        details="Tangent relationship must be proven before using this theorem"
                    ))

                # Verify arc exists in system
                normalized_arc = self.normalize_arc(arc)
                arc_var_name = f"arc_{normalized_arc}"
                if arc_var_name not in self.arcs:
                    return return_error(GeometricError(
                        tier=ErrorTier.TIER2_PREMISE_VIOLATION,
                        message=f"Arc {arc} not established in the system",
                        details="Arc must be defined before using this theorem"
                    ))

                return True, None
            else:
                return return_error(GeometricError(
                    tier=ErrorTier.TIER1_THEOREM_CALL_SYNTAX_VIOLATION,
                    message="these is no such version for the theorem",
                    details="these is no such version for the theorem circle_property_angle_of_osculation"
                ))


        elif theorem_name == "diameter_of_circle_judgment_right_angle":
            version = args[0]
            if version == "1":
                if len(args) < 3:
                    return return_error(GeometricError(
                        tier=ErrorTier.TIER1_THEOREM_CALL_SYNTAX_VIOLATION,
                        message="Insufficient arguments for diameter_of_circle_judgment_right_angle",
                        details="Expected: diameter_of_circle_judgment_right_angle(1, angle, circle)"
                    ))

                angle_token = args[1].strip()  # e.g., "BCA"
                circle_token = args[2].strip()  # e.g., "O"

                # Check for the cocircular fact
                cocircular_pattern = r'Cocircular\(' + re.escape(circle_token) + r',.*' + re.escape(
                    angle_token) + r'.*\)'
                alt_pattern = r'Cocircular\(' + re.escape(circle_token) + r',.*[' + ''.join(angle_token) + r'].*\)'

                cocircular_match = re.search(cocircular_pattern, premise) or re.search(alt_pattern, premise)
                if not cocircular_match:
                    return return_error(GeometricError(
                        tier=ErrorTier.TIER2_PREMISE_VIOLATION,
                        message=f"Missing Cocircular({circle_token},...) fact including points in {angle_token}",
                        details="diameter_of_circle_judgment_right_angle requires points to lie on the circle"
                    ))

                # Check if the cocircular fact is established in the system
                cocircular_found = False
                for fact in self.cocircular_facts:
                    if fact[0] == circle_token and all(point in ''.join(fact[1:]) for point in angle_token):
                        cocircular_found = True
                        break

                if not cocircular_found:
                    return return_error(GeometricError(
                        tier=ErrorTier.TIER2_PREMISE_VIOLATION,
                        message=f"Points in {angle_token} not proven to lie on circle {circle_token}",
                        details=f"Known cocircular facts: {self.cocircular_facts}"
                    ))

                # Check for the 90-degree angle fact
                angle_pattern = r'Equal\(MeasureOfAngle\(' + re.escape(angle_token) + r'\),90\)'
                angle_match = re.search(angle_pattern, premise)
                if not angle_match:
                    return return_error(GeometricError(
                        tier=ErrorTier.TIER2_PREMISE_VIOLATION,
                        message=f"Missing Equal(MeasureOfAngle({angle_token}),90) fact",
                        details="diameter_of_circle_judgment_right_angle requires a 90-degree angle"
                    ))

                # Check if the 90-degree angle is established in the solver
                angle_var = self.add_angle(angle_token[0], angle_token[1], angle_token[2])

                # Create temporary solver to check if angle must be 90
                temp_solver = Solver()
                for c in self.solver.assertions():
                    temp_solver.add(c)

                temp_solver.add(angle_var != 90)
                if temp_solver.check() != unsat:
                    return return_error(GeometricError(
                        tier=ErrorTier.TIER2_PREMISE_VIOLATION,
                        message=f"Angle {angle_token} is not proven to be 90 degrees",
                        details="The solver constraints do not force this angle to be 90 degrees"
                    ))

                return True, None
            else:
                return return_error(GeometricError(
                    tier=ErrorTier.TIER1_THEOREM_CALL_SYNTAX_VIOLATION,
                    message="these is no such version for the theorem",
                    details="these is no such version for the theorem diameter_of_circle_judgment_right_angle"
                ))

        elif theorem_name == "bisector_of_angle_judgment_angle_equal":
            version = args[0]
            if version == "1":
                if len(args) < 3:
                    return return_error(GeometricError(
                        tier=ErrorTier.TIER1_THEOREM_CALL_SYNTAX_VIOLATION,
                        message="Insufficient arguments for bisector_of_angle_judgment_angle_equal",
                        details="Expected: bisector_of_angle_judgment_angle_equal(1, bisector, angle)"
                    ))

                bisector = args[1].strip()  # e.g., "BD"
                angle_name = args[2].strip()  # e.g., "ABC"

                # Verify bisector is a ray from the angle's vertex
                if len(bisector) != 2 or len(angle_name) != 3:
                    return return_error(GeometricError(
                        tier=ErrorTier.TIER1_THEOREM_CALL_SYNTAX_VIOLATION,
                        message="Invalid format for bisector or angle",
                        details="Bisector should be a 2-letter ray and angle should be a 3-letter angle"
                    ))

                vertex = angle_name[1]  # Middle letter is the vertex
                if bisector[0] != vertex:
                    return return_error(GeometricError(
                        tier=ErrorTier.TIER2_PREMISE_VIOLATION,
                        message=f"Bisector {bisector} does not start from angle vertex {vertex}",
                        details="Angle bisector must start from the angle's vertex"
                    ))

                # Extract the two sub-angles created by the bisector
                left_arm = angle_name[0]  # First letter of the original angle
                right_arm = angle_name[2]  # Last letter of the original angle
                bisector_point = bisector[1]  # Second letter of the bisector

                # Construct the two sub-angles
                left_subangle = left_arm + vertex + bisector_point  # e.g., "ABD"
                right_subangle = bisector_point + vertex + right_arm  # e.g., "DBC"

                # Check if the angles are defined in the premise
                left_angle_match = re.search(r'Angle\(' + re.escape(left_subangle) + r'\)', premise)
                right_angle_match = re.search(r'Angle\(' + re.escape(right_subangle) + r'\)', premise)



                # Check for angle equality in the premise
                equality_pattern = r'Equal\(MeasureOfAngle\(' + re.escape(
                    left_subangle) + r'\),MeasureOfAngle\(' + re.escape(right_subangle) + r'\)\)'
                alt_equality_pattern = r'Equal\(MeasureOfAngle\(' + re.escape(
                    right_subangle) + r'\),MeasureOfAngle\(' + re.escape(left_subangle) + r'\)\)'

                if not (re.search(equality_pattern, premise) or re.search(alt_equality_pattern, premise)):
                    return return_error(GeometricError(
                        tier=ErrorTier.TIER2_PREMISE_VIOLATION,
                        message="Missing angle equality in premise",
                        details=f"Need Equal(MeasureOfAngle({left_subangle}),MeasureOfAngle({right_subangle})) in premise"
                    ))

                # Check if the angles are actually equal in the solver
                left_angle_var = self.add_angle(left_subangle[0], left_subangle[1], left_subangle[2])
                right_angle_var = self.add_angle(right_subangle[0], right_subangle[1], right_subangle[2])

                # Create temporary solver with current constraints
                temp_solver = Solver()
                for c in self.solver.assertions():
                    temp_solver.add(c)

                # Add the inequality constraint
                temp_solver.add(left_angle_var != right_angle_var)

                # If the system becomes unsatisfiable, the angles must be equal
                if temp_solver.check() == unsat:
                    # Angles are already constrained to be equal
                    pass
                else:
                    return return_error(GeometricError(
                        tier=ErrorTier.TIER2_PREMISE_VIOLATION,
                        message=f"Angles {left_subangle} and {right_subangle} not proven equal",
                        details="The solver's constraints do not force these angles to be equal"
                    ))

                return True, None
            else:
                return return_error(GeometricError(
                    tier=ErrorTier.TIER1_THEOREM_CALL_SYNTAX_VIOLATION,
                    message="these is no such version for the theorem",
                    details="these is no such version for the theorem bisector_of_angle_judgment_angle_equal"
                ))

        elif theorem_name == "tangent_of_circle_property_length_equal":
            version = args[0]
            if version == "1":
                if len(args) < 4:
                    return return_error(GeometricError(
                        tier=ErrorTier.TIER1_THEOREM_CALL_SYNTAX_VIOLATION,
                        message="Insufficient arguments for tangent_of_circle_property_length_equal",
                        details="Expected: tangent_of_circle_property_length_equal(1, tangent1, tangent2, circle)"
                    ))

                tangent1 = args[1].strip()  # e.g., "AM"
                tangent2 = args[2].strip()  # e.g., "AG"
                circle = args[3].strip()  # e.g., "O"

                # Verify the tangent facts in the premise
                tangent1_match = re.search(
                    r'IsTangentOfCircle\(' + re.escape(tangent1) + ',' + re.escape(circle) + r'\)', premise)
                tangent2_match = re.search(
                    r'IsTangentOfCircle\(' + re.escape(tangent2) + ',' + re.escape(circle) + r'\)', premise)

                if not tangent1_match:
                    return return_error(GeometricError(
                        tier=ErrorTier.TIER2_PREMISE_VIOLATION,
                        message=f"Missing IsTangentOfCircle({tangent1},{circle}) in premise",
                        details=f"Both tangent lines must be established as tangents to the circle"
                    ))

                if not tangent2_match:
                    return return_error(GeometricError(
                        tier=ErrorTier.TIER2_PREMISE_VIOLATION,
                        message=f"Missing IsTangentOfCircle({tangent2},{circle}) in premise",
                        details=f"Both tangent lines must be established as tangents to the circle"
                    ))

                # Verify both segments start from the same point
                if tangent1[0] != tangent2[0]:
                    return return_error(GeometricError(
                        tier=ErrorTier.TIER2_PREMISE_VIOLATION,
                        message=f"Tangent segments {tangent1} and {tangent2} do not share the same starting point",
                        details=f"For this theorem, both tangent segments must start from the same external point"
                    ))

                # Also check if these tangent facts are stored in the system
                if (tangent1, circle) not in self.tangent_facts:
                    return return_error(GeometricError(
                        tier=ErrorTier.TIER2_PREMISE_VIOLATION,
                        message=f"Tangent fact IsTangentOfCircle({tangent1},{circle}) not established in the system",
                        details=f"Known tangent facts: {self.tangent_facts}"
                    ))

                if (tangent2, circle) not in self.tangent_facts:
                    return return_error(GeometricError(
                        tier=ErrorTier.TIER2_PREMISE_VIOLATION,
                        message=f"Tangent fact IsTangentOfCircle({tangent2},{circle}) not established in the system",
                        details=f"Known tangent facts: {self.tangent_facts}"
                    ))

                return True, None
            else:
                return return_error(GeometricError(
                    tier=ErrorTier.TIER1_THEOREM_CALL_SYNTAX_VIOLATION,
                    message="these is no such version for the theorem",
                    details="these is no such version for the theorem tangent_of_circle_property_length_equal"
                ))

        elif theorem_name == "rectangle_judgment_right_angle":
            version = args[0]
            if version == "1":
                if len(args) < 2:
                    return return_error(GeometricError(
                        tier=ErrorTier.TIER1_THEOREM_CALL_SYNTAX_VIOLATION,
                        message="Missing quadrilateral argument for rectangle_judgment_right_angle",
                        details="Expected: rectangle_judgment_right_angle(1, quadrilateral)"
                    ))

                quad = args[1].strip()  # e.g., "ABCD"

                # Check if the quadrilateral is defined as a parallelogram in the premise
                parallelogram_match = re.search(r'Parallelogram\(' + re.escape(quad) + r'\)', premise)
                if not parallelogram_match:
                    return return_error(GeometricError(
                        tier=ErrorTier.TIER2_PREMISE_VIOLATION,
                        message=f"Quadrilateral {quad} not established as a parallelogram in premise",
                        details="rectangle_judgment_right_angle requires Parallelogram(...) in premise"
                    ))

                # Check if the quadrilateral is defined as a parallelogram in the system
                if not hasattr(self, "parallelograms"):
                    return return_error(GeometricError(
                        tier=ErrorTier.TIER2_PREMISE_VIOLATION,
                        message="No parallelograms defined in the system",
                        details="rectangle_judgment_right_angle requires quadrilateral to be a parallelogram"
                    ))

                # Check for any cyclic variation of the quadrilateral in parallelograms
                quad_variations = get_cyclic_variations(quad)
                if not any(var in self.parallelograms for var in quad_variations):
                    return return_error(GeometricError(
                        tier=ErrorTier.TIER2_PREMISE_VIOLATION,
                        message=f"Quadrilateral {quad} not proven to be a parallelogram",
                        details=f"Known parallelograms: {self.parallelograms}"
                    ))

                # Check for right angle in the premise
                right_angle_match = re.search(r'Equal\(MeasureOfAngle\((\w{3})\),90\)', premise)
                if not right_angle_match:
                    return return_error(GeometricError(
                        tier=ErrorTier.TIER2_PREMISE_VIOLATION,
                        message="Missing right angle in premise",
                        details="rectangle_judgment_right_angle requires one angle to be 90 degrees"
                    ))

                # Check that the angle is from the quadrilateral
                angle_name = right_angle_match.group(1)
                if not all(point in quad for point in angle_name):
                    return return_error(GeometricError(
                        tier=ErrorTier.TIER2_PREMISE_VIOLATION,
                        message=f"Angle {angle_name} does not belong to quadrilateral {quad}",
                        details="The right angle must be an angle of the quadrilateral"
                    ))

                # Verify the angle is actually 90 degrees in the solver
                angle_var = self.add_angle(angle_name[0], angle_name[1], angle_name[2])
                temp_solver = Solver()
                for c in self.solver.assertions():
                    temp_solver.add(c)

                # Check if the angle must be 90 degrees
                temp_solver.add(angle_var != 90)
                if temp_solver.check() != unsat:
                    return return_error(GeometricError(
                        tier=ErrorTier.TIER2_PREMISE_VIOLATION,
                        message=f"Angle {angle_name} is not constrained to be 90°",
                        details="The right angle constraint must be enforced by the solver"
                    ))

                return True, None
            else:
                return return_error(GeometricError(
                    tier=ErrorTier.TIER1_THEOREM_CALL_SYNTAX_VIOLATION,
                    message=f"Unsupported version for rectangle_judgment_right_angle",
                    details="Unsupported version for rectangle_judgment_right_angle"
                ))


        elif theorem_name == "round_arc":
            version = args[0]
            if version == "1":
                if len(args) < 3:
                    return return_error(GeometricError(
                        tier=ErrorTier.TIER1_THEOREM_CALL_SYNTAX_VIOLATION,
                        message="Insufficient arguments for round_arc",
                        details="Expected: round_arc(1, arc1, arc2)"
                    ))

                arc1, arc2 = args[1].strip(), args[2].strip()

                # Check that both arcs are defined in the premise
                arc1_match = re.search(r'Arc\(' + re.escape(arc1) + r'\)', premise)
                arc2_match = re.search(r'Arc\(' + re.escape(arc2) + r'\)', premise)

                if not arc1_match:
                    return return_error(GeometricError(
                        tier=ErrorTier.TIER2_PREMISE_VIOLATION,
                        message=f"Missing Arc({arc1}) in premise",
                        details="round_arc requires both arcs to be defined"
                    ))

                if not arc2_match:
                    return return_error(GeometricError(
                        tier=ErrorTier.TIER2_PREMISE_VIOLATION,
                        message=f"Missing Arc({arc2}) in premise",
                        details="round_arc requires both arcs to be defined"
                    ))

                # Verify that both arcs share the same circle (first character)
                if arc1[0] != arc2[0]:
                    return return_error(GeometricError(
                        tier=ErrorTier.TIER2_PREMISE_VIOLATION,
                        message=f"Arcs {arc1} and {arc2} do not share the same circle",
                        details="round_arc requires both arcs to be on the same circle"
                    ))

                # Check if the arcs are defined in the system
                normalized_arc1 = self.normalize_arc(arc1)
                normalized_arc2 = self.normalize_arc(arc2)

                arc_var_name1 = f"arc_{normalized_arc1}"
                arc_var_name2 = f"arc_{normalized_arc2}"

                if arc_var_name1 not in self.arcs:
                    return return_error(GeometricError(
                        tier=ErrorTier.TIER2_PREMISE_VIOLATION,
                        message=f"Arc {arc1} not defined in the system",
                        details=f"Known arcs: {list(self.arcs.keys())}"
                    ))

                if arc_var_name2 not in self.arcs:
                    return return_error(GeometricError(
                        tier=ErrorTier.TIER2_PREMISE_VIOLATION,
                        message=f"Arc {arc2} not defined in the system",
                        details=f"Known arcs: {list(self.arcs.keys())}"
                    ))

                return True, None
            else:
                return return_error(GeometricError(
                    tier=ErrorTier.TIER1_THEOREM_CALL_SYNTAX_VIOLATION,
                    message=f"Unsupported version for round_arc",
                    details="Unsupported version for round_arc"
                ))

        elif theorem_name == "quadrilateral_perimeter_formula":
            version = args[0]
            if version == "1":
                if len(args) < 2:
                    return return_error(GeometricError(
                        tier=ErrorTier.TIER1_THEOREM_CALL_SYNTAX_VIOLATION,
                        message="Missing quadrilateral name for quadrilateral_perimeter_formula",
                        details="Expected: quadrilateral_perimeter_formula(1, quadrilateral)"
                    ))

                quad = args[1].strip()  # e.g., "ABCD"

                # Verify that the quadrilateral is defined in the premise
                polygon_match = re.search(r'Polygon\(' + re.escape(quad) + r'\)', premise)

                if not polygon_match:
                    return return_error(GeometricError(
                        tier=ErrorTier.TIER2_PREMISE_VIOLATION,
                        message=f"Missing Polygon({quad}) in premise",
                        details="The quadrilateral must be established as a polygon"
                    ))

                # Also check if the quadrilateral is stored in the system's polygons
                if quad not in self.polygons and self.normalize_quadrilateral(quad) not in self.polygons:
                    return return_error(GeometricError(
                        tier=ErrorTier.TIER2_PREMISE_VIOLATION,
                        message=f"Polygon {quad} is not defined in the system",
                        details=f"Known polygons: {self.polygons}"
                    ))

                return True, None
            else:
                return return_error(GeometricError(
                    tier=ErrorTier.TIER1_THEOREM_CALL_SYNTAX_VIOLATION,
                    message="these is no such version for the theorem quadrilateral_perimeter_formula",
                    details="these is no such version for the theorem quadrilateral_perimeter_formula"
                ))

        elif theorem_name == "equilateral_triangle_property_angle":
            version = args[0]
            if version == "1":
                if len(args) < 2:
                    return return_error(GeometricError(
                        tier=ErrorTier.TIER1_THEOREM_CALL_SYNTAX_VIOLATION,
                        message="Missing triangle argument for equilateral_triangle_property_angle",
                        details="Expected: equilateral_triangle_property_angle(1, triangle)"
                    ))

                triangle = args[1].strip()  # e.g., "ABC"

                # Check if triangle is defined as equilateral in the premise
                equilateral_match = re.search(r'EquilateralTriangle\(' + re.escape(triangle) + r'\)', premise)
                if not equilateral_match:
                    return return_error(GeometricError(
                        tier=ErrorTier.TIER2_PREMISE_VIOLATION,
                        message=f"Triangle {triangle} not established as equilateral in premise",
                        details="equilateral_triangle_property_angle requires EquilateralTriangle(...) in premise"
                    ))

                # Check if triangle is defined as equilateral in the system
                if not hasattr(self, "equilateral_triangles"):
                    return return_error(GeometricError(
                        tier=ErrorTier.TIER2_PREMISE_VIOLATION,
                        message=f"No equilateral triangles defined in the system",
                        details="equilateral_triangle_property_angle requires triangle to be equilateral"
                    ))

                # Generate all cyclic rotations of the triangle
                triangle_rotations = [triangle[i:] + triangle[:i] for i in range(len(triangle))]
                if not any(rot in self.equilateral_triangles for rot in triangle_rotations):
                    return return_error(GeometricError(
                        tier=ErrorTier.TIER2_PREMISE_VIOLATION,
                        message=f"Triangle {triangle} not proven equilateral",
                        details=f"Known equilateral triangles: {self.equilateral_triangles}"
                    ))

                return True, None
            else:
                return return_error(GeometricError(
                    tier=ErrorTier.TIER1_THEOREM_CALL_SYNTAX_VIOLATION,
                    message=f"Unsupported version for equilateral_triangle_property_angle",
                    details="Unsupported version for equilateral_triangle_property_angle"
                ))

        elif theorem_name == "congruent_triangle_judgment_aas":
            version = args[0]
            if version in {"1", "2", "3"}:
                if len(args) < 3:
                    return return_error(GeometricError(
                        tier=ErrorTier.TIER1_THEOREM_CALL_SYNTAX_VIOLATION,
                        message="Insufficient arguments for congruent_triangle_judgment_aas",
                        details=f"Expected: congruent_triangle_judgment_aas({version}, triangle1, triangle2)"
                    ))

                tri1, tri2 = args[1].strip(), args[2].strip()

                # Check if both triangles exist as polygons
                if self.normalize_triangle(tri1) not in self.polygons:
                    return return_error(GeometricError(
                        tier=ErrorTier.TIER2_PREMISE_VIOLATION,
                        message=f"Triangle {tri1} not defined",
                        details=f"Known polygons: {self.polygons}"
                    ))

                if self.normalize_triangle(tri2) not in self.polygons:
                    return return_error(GeometricError(
                        tier=ErrorTier.TIER2_PREMISE_VIOLATION,
                        message=f"Triangle {tri2} not defined",
                        details=f"Known polygons: {self.polygons}"
                    ))

                # Check for polygon definitions in premise
                polygon_matches = re.findall(r'Polygon\((\w+)\)', premise)
                if len(polygon_matches) < 2:
                    return return_error(GeometricError(
                        tier=ErrorTier.TIER2_PREMISE_VIOLATION,
                        message="Missing polygon definitions in premise",
                        details="congruent_triangle_judgment_aas requires both triangles to be defined"
                    ))

                # Check for angle equalities
                angle_equalities = re.findall(r'Equal\(MeasureOfAngle\((\w+)\),MeasureOfAngle\((\w+)\)\)', premise)
                if len(angle_equalities) < 2:
                    return return_error(GeometricError(
                        tier=ErrorTier.TIER2_PREMISE_VIOLATION,
                        message="Insufficient angle equalities in premise",
                        details="congruent_triangle_judgment_aas requires at least 2 equal angle pairs"
                    ))

                # Check for side equality - differs by version
                if version == "1":
                    # Check first sides of triangles (AB and DE)
                    side1 = tri1[0] + tri1[1]  # e.g., "AB"
                    side2 = tri2[0] + tri2[1]  # e.g., "DE"
                    side_pattern = r'Equal\(LengthOfLine\(' + re.escape(side1) + r'\),LengthOfLine\(' + re.escape(
                        side2) + r'\)\)'
                    if not re.search(side_pattern, premise):
                        return return_error(GeometricError(
                            tier=ErrorTier.TIER2_PREMISE_VIOLATION,
                            message=f"Missing side equality in premise for version 1",
                            details=f"Version 1 requires Equal(LengthOfLine({side1}),LengthOfLine({side2}))"
                        ))
                elif version == "2":
                    # Check second sides of triangles (BC and EF)
                    side1 = tri1[1] + tri1[2]  # e.g., "BC"
                    side2 = tri2[1] + tri2[2]  # e.g., "EF"
                    side_pattern = r'Equal\(LengthOfLine\(' + re.escape(side1) + r'\),LengthOfLine\(' + re.escape(
                        side2) + r'\)\)'
                    if not re.search(side_pattern, premise):
                        return return_error(GeometricError(
                            tier=ErrorTier.TIER2_PREMISE_VIOLATION,
                            message=f"Missing side equality in premise for version 2",
                            details=f"Version 2 requires Equal(LengthOfLine({side1}),LengthOfLine({side2}))"
                        ))
                elif version == "3":
                    # Check third sides of triangles (AC and DF)
                    side1 = tri1[0] + tri1[2]  # e.g., "AC"
                    side2 = tri2[0] + tri2[2]  # e.g., "DF"
                    side_pattern = r'Equal\(LengthOfLine\(' + re.escape(side1) + r'\),LengthOfLine\(' + re.escape(
                        side2) + r'\)\)'
                    if not re.search(side_pattern, premise):
                        return return_error(GeometricError(
                            tier=ErrorTier.TIER2_PREMISE_VIOLATION,
                            message=f"Missing side equality in premise for version 3",
                            details=f"Version 3 requires Equal(LengthOfLine({side1}),LengthOfLine({side2}))"
                        ))

                return True, None
            else:
                return return_error(GeometricError(
                    tier=ErrorTier.TIER1_THEOREM_CALL_SYNTAX_VIOLATION,
                    message="these is no such version for the theorem",
                    details="these is no such version for the theorem congruent_triangle_judgment_aas"
                ))


        elif theorem_name == "similar_triangle_property_area_square_ratio":
            version = args[0]
            if version == "1":
                if len(args) < 3:
                    return return_error(GeometricError(
                        tier=ErrorTier.TIER1_THEOREM_CALL_SYNTAX_VIOLATION,
                        message="Insufficient arguments for similar_triangle_property_area_square_ratio",
                        details="Expected: similar_triangle_property_area_square_ratio(1, triangle1, triangle2)"
                    ))

                tri1, tri2 = args[1].strip(), args[2].strip()

                # Check if the premise states that the triangles are similar
                similar_match = re.search(r'SimilarBetweenTriangle\((\w+),(\w+)\)', premise)
                if not similar_match:
                    return return_error(GeometricError(
                        tier=ErrorTier.TIER2_PREMISE_VIOLATION,
                        message="Missing similar triangles relationship in premise",
                        details="similar_triangle_property_area_square_ratio requires SimilarBetweenTriangle(...)"
                    ))

                premise_tri1, premise_tri2 = similar_match.groups()

                # Check if the triangles in the premise match those in the function call
                norm_call_triangles = self.normalize_similar_triangles(tri1, tri2)
                norm_premise_triangles = self.normalize_similar_triangles(premise_tri1, premise_tri2)

                if norm_call_triangles != norm_premise_triangles:
                    return return_error(GeometricError(
                        tier=ErrorTier.TIER2_PREMISE_VIOLATION,
                        message=f"Triangle mismatch: call uses {tri1},{tri2} but premise has {premise_tri1},{premise_tri2}",
                        details="Triangles in the theorem call must match those in the premise"
                    ))

                # Check if the triangles are actually marked as similar in the system
                if not self.are_triangles_similar(tri1, tri2):
                    return return_error(GeometricError(
                        tier=ErrorTier.TIER2_PREMISE_VIOLATION,
                        message=f"Triangles {tri1} and {tri2} not proven similar",
                        details=f"Known similar triangle pairs: {self.similar_triangles}"
                    ))

                return True, None
            else:
                return return_error(GeometricError(
                    tier=ErrorTier.TIER1_THEOREM_CALL_SYNTAX_VIOLATION,
                    message="these is no such version for the theorem",
                    details="these is no such version for the theorem similar_triangle_property_area_square_ratio"
                ))


        elif theorem_name == "midsegment_of_quadrilateral_property_length":
            version = args[0]
            if version == "1":
                if len(args) < 3:
                    return return_error(GeometricError(
                        tier=ErrorTier.TIER1_THEOREM_CALL_SYNTAX_VIOLATION,
                        message="Insufficient arguments for midsegment_of_quadrilateral_property_length",
                        details="Expected: midsegment_of_quadrilateral_property_length(1, segment, quadrilateral)"
                    ))

                segment = args[1].strip()
                quad = args[2].strip()

                # Try to extract the midsegment relationship from the premise
                midsegment_match = re.search(
                    r'IsMidsegmentOfQuadrilateral\(' + re.escape(segment) + ',' + re.escape(quad) + r'\)', premise)

                # If not found directly in premise, check if it's in our stored data with permutations
                if not midsegment_match:
                    if not self.check_midsegment_with_permutations(segment, quad):
                        return return_error(GeometricError(
                            tier=ErrorTier.TIER2_PREMISE_VIOLATION,
                            message=f"Missing IsMidsegmentOfQuadrilateral({segment},{quad}) in premise",
                            details="The line must be established as a midsegment of the quadrilateral"
                        ))

                return True, None
            else:
                return return_error(GeometricError(
                    tier=ErrorTier.TIER1_THEOREM_CALL_SYNTAX_VIOLATION,
                    message="these is no such version for the theorem",
                    details="these is no such version for the theorem midsegment_of_quadrilateral_property_length"
                ))



        elif theorem_name == "parallelogram_area_formula_sine":
            version = args[0]
            if version == "1":
                if len(args) < 2:
                    return return_error(GeometricError(
                        tier=ErrorTier.TIER1_THEOREM_CALL_SYNTAX_VIOLATION,
                        message="Missing parallelogram name for parallelogram_area_formula_sine",
                        details="Expected parallelogram_area_formula_sine(1, quadrilateral)"
                    ))

                quad_name = args[1].strip()

                # Parse the premise for the parallelogram declaration
                parallelogram_match = re.search(r'Parallelogram\((\w+)\)', premise)
                if not parallelogram_match:
                    return return_error(GeometricError(
                        tier=ErrorTier.TIER2_PREMISE_VIOLATION,
                        message="Missing parallelogram declaration in premise",
                        details=f"Premise must contain Parallelogram({quad_name})"
                    ))

                premise_para = parallelogram_match.group(1)
                if premise_para != quad_name:
                    return return_error(GeometricError(
                        tier=ErrorTier.TIER2_PREMISE_VIOLATION,
                        message=f"Parallelogram in premise ({premise_para}) doesn't match the one in theorem call ({quad_name})",
                        details="The parallelogram names must match"
                    ))

                # Check if this parallelogram is defined in the system
                # This checks if any cyclic variation of the parallelogram is in self.parallelograms
                if not any(var in self.parallelograms for var in get_cyclic_variations(quad_name)):
                    return return_error(GeometricError(
                        tier=ErrorTier.TIER2_PREMISE_VIOLATION,
                        message=f"Parallelogram {quad_name} is not defined in the system",
                        details=f"Available parallelograms: {', '.join(self.parallelograms)}"
                    ))

                return True, None
            else:
                return return_error(GeometricError(
                    tier=ErrorTier.TIER1_THEOREM_CALL_SYNTAX_VIOLATION,
                    message="these is no such version for the theorem",
                    details="these is no such version for the theorem parallelogram_area_formula_sine"
                ))


        elif theorem_name == "arc_addition_measure":
            version = args[0]
            if version == "1":
                if len(args) < 3:
                    return return_error(GeometricError(
                        tier=ErrorTier.TIER1_THEOREM_CALL_SYNTAX_VIOLATION,
                        message="Insufficient arguments for arc_addition_measure",
                        details="Expected: arc_addition_measure(1, arc1, arc2)"
                    ))

                arc1_token = args[1].strip()  # e.g., "ODA"
                arc2_token = args[2].strip()  # e.g., "OAB"

                # Parse the premise to check if it contains the required Arc facts
                premise_parts = premise.split('&')

                # Check for the three required arcs in the premise
                arc_parts = [p for p in premise_parts if p.startswith("Arc(")]
                if len(arc_parts) < 3:
                    return return_error(GeometricError(
                        tier=ErrorTier.TIER2_PREMISE_VIOLATION,
                        message="Missing arc facts in premise",
                        details="arc_addition_measure requires three Arc facts (two component arcs and the total arc)"
                    ))

                # Verify that the arcs mentioned in the theorem call appear in the premise
                arc1_found = any(p == f"Arc({arc1_token})" for p in arc_parts)
                arc2_found = any(p == f"Arc({arc2_token})" for p in arc_parts)

                if not arc1_found:
                    return return_error(GeometricError(
                        tier=ErrorTier.TIER2_PREMISE_VIOLATION,
                        message=f"Arc({arc1_token}) not found in premise",
                        details=f"The first component arc must be declared in the premise"
                    ))

                if not arc2_found:
                    return return_error(GeometricError(
                        tier=ErrorTier.TIER2_PREMISE_VIOLATION,
                        message=f"Arc({arc2_token}) not found in premise",
                        details=f"The second component arc must be declared in the premise"
                    ))

                # Extract the total arc from the third arc in the premise
                # The total arc should be the remaining arc that isn't arc1 or arc2
                total_arc_token = None
                for p in arc_parts:
                    arc_match = re.match(r'Arc\((\w+)\)', p)
                    if arc_match:
                        current_arc = arc_match.group(1)
                        if current_arc != arc1_token and current_arc != arc2_token:
                            total_arc_token = current_arc
                            break

                if not total_arc_token:
                    return return_error(GeometricError(
                        tier=ErrorTier.TIER2_PREMISE_VIOLATION,
                        message="Could not identify the total arc in premise",
                        details="The premise must contain a third distinct arc that will be the sum of the two component arcs"
                    ))

                # Verify that all arcs exist in the system
                normalized_arc1 = self.normalize_arc(arc1_token)
                normalized_arc2 = self.normalize_arc(arc2_token)
                normalized_total = self.normalize_arc(total_arc_token)

                arc_var_name1 = f"arc_{normalized_arc1}"
                arc_var_name2 = f"arc_{normalized_arc2}"
                total_arc_var_name = f"arc_{normalized_total}"

                # Check if arcs have been declared
                arcs_ok = True
                missing_arcs = []

                if arc_var_name1 not in self.arcs:
                    arcs_ok = False
                    missing_arcs.append(arc1_token)

                if arc_var_name2 not in self.arcs:
                    arcs_ok = False
                    missing_arcs.append(arc2_token)

                if total_arc_var_name not in self.arcs:
                    arcs_ok = False
                    missing_arcs.append(total_arc_token)

                if not arcs_ok:
                    return return_error(GeometricError(
                        tier=ErrorTier.TIER2_PREMISE_VIOLATION,
                        message=f"One or more arcs not defined in the system: {', '.join(missing_arcs)}",
                        details="All arcs must be properly defined before using arc_addition_measure"
                    ))

                return True, None
            else:
                return return_error(GeometricError(
                    tier=ErrorTier.TIER1_THEOREM_CALL_SYNTAX_VIOLATION,
                    message="these is no such version for the theorem",
                    details="these is no such version for the theorem arc_addition_measure"
                ))



        elif theorem_name == "isosceles_triangle_property_line_coincidence":

            version = args[0]

            if version in {"1", "2", "3"}:

                if len(args) < 3:
                    return return_error(GeometricError(

                        tier=ErrorTier.TIER1_THEOREM_CALL_SYNTAX_VIOLATION,

                        message="Insufficient arguments for isosceles_triangle_property_line_coincidence",

                        details=f"Expected: isosceles_triangle_property_line_coincidence({version}, triangle, point)"

                    ))

                triangle = args[1].strip()  # e.g., "ABC"

                point = args[2].strip()  # e.g., "M"

                line = triangle[0] + point  # e.g., "AM"

                # Parse the premise components

                premise_parts = premise.split('&')

                # Check for IsoscelesTriangle fact (required in all versions)

                isosceles_found = False

                for part in premise_parts:

                    if part.startswith("IsoscelesTriangle"):

                        match = re.match(r'IsoscelesTriangle\((\w+)\)', part)

                        if match and match.group(1) == triangle:
                            isosceles_found = True

                            break

                # Also check our stored isosceles triangles

                if not isosceles_found and hasattr(self, "isosceles_triangles"):

                    # Check if any rotation of the triangle is in our isosceles set

                    triangle_rotations = [triangle[i:] + triangle[:i] for i in range(len(triangle))]

                    if any(rot in self.isosceles_triangles for rot in triangle_rotations):
                        isosceles_found = True

                if not isosceles_found:
                    return return_error(GeometricError(

                        tier=ErrorTier.TIER2_PREMISE_VIOLATION,

                        message=f"Triangle {triangle} is not established as isosceles",

                        details=f"Need IsoscelesTriangle({triangle}) in premise or previous theorem"

                    ))

                # Version-specific checks

                if version == "1":

                    # Check for IsAltitudeOfTriangle fact

                    altitude_found = False

                    for part in premise_parts:

                        if part.startswith("IsAltitudeOfTriangle"):

                            match = re.match(r'IsAltitudeOfTriangle\((\w+),(\w+)\)', part)

                            if match and match.group(1) == line and match.group(2) == triangle:
                                altitude_found = True

                                break

                    # Also check stored altitude data

                    if not altitude_found and hasattr(self, "triangle_altitudes"):

                        if triangle in self.triangle_altitudes and line in self.triangle_altitudes[triangle]:
                            altitude_found = True

                    if not altitude_found:
                        return return_error(GeometricError(

                            tier=ErrorTier.TIER2_PREMISE_VIOLATION,

                            message=f"Line {line} is not established as an altitude of triangle {triangle}",

                            details=f"Version 1 requires IsAltitudeOfTriangle({line},{triangle})"

                        ))



                elif version == "2":

                    # Conclusions: IsAltitudeOfTriangle(AM,ABC), IsBisectorOfAngle(AM,CAB)

                    # --- Process the altitude conclusion ---

                    if not hasattr(self, "triangle_altitudes"):
                        self.triangle_altitudes = {}

                    if triangle not in self.triangle_altitudes:
                        self.triangle_altitudes[triangle] = []

                    self.triangle_altitudes[triangle].append(line)

                    altitude_start = line[0]  # Vertex from which altitude starts (e.g., B in BO)

                    altitude_end = line[1]  # Foot of the altitude (e.g., O in BO)

                    opposite_vertices = [v for v in triangle if
                                         v != altitude_start]  # Base vertices (e.g., C, A for BO in BCA)

                    # --- CORRECTED ANGLE FORMATION ---

                    # The right angles are at the foot of the altitude (altitude_end)

                    # Angle 1: altitude_start -> altitude_end -> opposite_vertex1 (e.g., B-O-C)

                    # Angle 2: altitude_start -> altitude_end -> opposite_vertex2 (e.g., B-O-A)

                    if len(opposite_vertices) == 2:

                        angle_name1 = altitude_start + altitude_end + opposite_vertices[0]  # e.g., BOC

                        angle_var1 = self.add_angle(angle_name1[0], angle_name1[1], angle_name1[2])

                        self.solver.add(angle_var1 == 90)

                        print(
                            f"Added 90° angle constraint for altitude: angle {self.normalize_angle_name(angle_name1)} = 90°")

                        angle_name2 = altitude_start + altitude_end + opposite_vertices[1]  # e.g., BOA

                        angle_var2 = self.add_angle(angle_name2[0], angle_name2[1], angle_name2[2])

                        self.solver.add(angle_var2 == 90)

                        print(
                            f"Added 90° angle constraint for altitude: angle {self.normalize_angle_name(angle_name2)} = 90°")

                    else:

                        print(
                            f"Warning: Could not determine opposite vertices correctly for altitude {line} in triangle {triangle}")

                    # --- END CORRECTION ---

                    # --- Process the angle bisector conclusion (This part was already correct) ---

                    if not hasattr(self, "angle_bisectors"):
                        self.angle_bisectors = []

                    # Construct the angle being bisected (e.g., CBA for bisector BO in triangle BCA)

                    bisected_angle_name = opposite_vertices[0] + altitude_start + opposite_vertices[1]  # e.g., CAB

                    self.angle_bisectors.append((line, bisected_angle_name))

                    # Add angle bisector constraints (e.g., CBO = OBA)

                    vertex = altitude_start  # e.g., B

                    angle_side1 = opposite_vertices[0]  # e.g., C

                    angle_side2 = opposite_vertices[1]  # e.g., A

                    bisector_other = altitude_end  # e.g., O

                    angle1 = angle_side1 + vertex + bisector_other  # e.g., CBO

                    angle2 = bisector_other + vertex + angle_side2  # e.g., OBA

                    angle1_var = self.add_angle(angle1[0], angle1[1], angle1[2])

                    angle2_var = self.add_angle(angle2[0], angle2[1], angle2[2])

                    self.solver.add(angle1_var == angle2_var)

                    print(
                        f"Added angle bisector constraint: angle {self.normalize_angle_name(angle1)} = angle {self.normalize_angle_name(angle2)}")


                elif version == "3":

                    # Check for Collinear fact

                    opposite_vertices = [v for v in triangle if v != line[0]]  # e.g., ["B", "C"]

                    expected_collinear = point + opposite_vertices[0] + opposite_vertices[1]  # e.g., "MBC"

                    collinear_found = False

                    for part in premise_parts:

                        if part.startswith("Collinear"):

                            match = re.match(r'Collinear\((\w+)\)', part)

                            if match:

                                collinear_str = match.group(1)

                                if self.normalize_collinear_points(collinear_str) == self.normalize_collinear_points(
                                        expected_collinear):
                                    collinear_found = True

                                    break

                    # Also check stored collinear facts

                    if not collinear_found:

                        for fact in self.collinear_facts:

                            if self.normalize_collinear_points(''.join(fact)) == self.normalize_collinear_points(
                                    expected_collinear):
                                collinear_found = True

                                break

                    if not collinear_found:
                        return return_error(GeometricError(

                            tier=ErrorTier.TIER2_PREMISE_VIOLATION,

                            message=f"Points {expected_collinear} are not proven collinear",

                            details=f"Version 3 requires Collinear({expected_collinear})"

                        ))

                    # Check for IsBisectorOfAngle fact

                    angle_name = opposite_vertices[0] + line[0] + opposite_vertices[1]  # "BAC" or "CAB"

                    expected_bisector = f"IsBisectorOfAngle({line},{angle_name})"

                    bisector_found = False

                    for part in premise_parts:

                        if part.startswith("IsBisectorOfAngle"):

                            if part == expected_bisector:
                                bisector_found = True

                                break

                    # Also check stored angle bisectors

                    if not bisector_found and hasattr(self, "angle_bisectors"):

                        if (line, angle_name) in self.angle_bisectors:
                            bisector_found = True

                    if not bisector_found:
                        return return_error(GeometricError(

                            tier=ErrorTier.TIER2_PREMISE_VIOLATION,

                            message=f"Line {line} is not established as a bisector of angle {angle_name}",

                            details=f"Version 3 requires {expected_bisector}"

                        ))

                # Validate that the triangle is well-formed (3 distinct vertices)

                if len(triangle) != 3 or len(set(triangle)) != 3:
                    return return_error(GeometricError(

                        tier=ErrorTier.TIER2_PREMISE_VIOLATION,

                        message=f"Invalid triangle {triangle}",

                        details="Triangle must have exactly 3 distinct vertices"

                    ))

                return True, None

            else:

                return return_error(GeometricError(
                    tier=ErrorTier.TIER1_THEOREM_CALL_SYNTAX_VIOLATION,
                    message="these is no such version for the theorem",
                    details="these is no such version for the theorem isosceles_triangle_property_line_coincidence"
                ))


        elif theorem_name == "diameter_of_circle_judgment_pass_centre":
            version = args[0]
            if version == "1":
                if len(args) < 3:
                    return return_error(GeometricError(
                        tier=ErrorTier.TIER1_THEOREM_CALL_SYNTAX_VIOLATION,
                        message="Insufficient arguments for diameter_of_circle_judgment_pass_centre",
                        details="Expected: diameter_of_circle_judgment_pass_centre(1, collinear_points, circle)"
                    ))

                collinear_points = args[1].strip()  # e.g., "AOB"
                circle_token = args[2].strip()  # e.g., "O"

                # Check that the circle center is included in the collinear points
                if circle_token not in collinear_points:
                    return return_error(GeometricError(
                        tier=ErrorTier.TIER2_PREMISE_VIOLATION,
                        message=f"Circle center {circle_token} not in collinear points {collinear_points}",
                        details="For a diameter, the collinear points must include the center of the circle"
                    ))

                # Parse the premise components
                premise_parts = premise.split('&')

                # Check for Cocircular fact
                cocircular_found = False
                for part in premise_parts:
                    if part.startswith("Cocircular"):
                        match = re.match(r'Cocircular\((\w+),(\w+)\)', part)
                        if match:
                            circ, points = match.groups()
                            if circ == circle_token:
                                # The endpoints of the potential diameter
                                endpoints = [p for p in collinear_points if p != circle_token]

                                # Check if all endpoints are on the circle
                                if all(p in points for p in endpoints):
                                    cocircular_found = True
                                    break

                if not cocircular_found:
                    return return_error(GeometricError(
                        tier=ErrorTier.TIER2_PREMISE_VIOLATION,
                        message="Missing valid Cocircular fact in premise",
                        details=f"Points in {collinear_points} excluding {circle_token} must be on circle {circle_token}"
                    ))

                # Check for Collinear fact
                collinear_found = False
                for part in premise_parts:
                    if part.startswith("Collinear"):
                        match = re.match(r'Collinear\((\w+)\)', part)
                        if match:
                            col_points = match.group(1)
                            # Normalize both collinear strings for comparison
                            norm_premise = self.normalize_collinear_points(col_points)
                            norm_arg = self.normalize_collinear_points(collinear_points)

                            if norm_premise == norm_arg:
                                collinear_found = True
                                break

                            # Also check if the collinear points in the premise contain all points in the argument
                            if all(p in col_points for p in collinear_points):
                                collinear_found = True
                                break

                if not collinear_found:
                    stored_collinear = [''.join(fact) for fact in self.collinear_facts]
                    return return_error(GeometricError(
                        tier=ErrorTier.TIER2_PREMISE_VIOLATION,
                        message=f"Collinear({collinear_points}) not established",
                        details=f"Known collinear facts: {stored_collinear}"
                    ))

                # Check for IsCentreOfCircle fact
                center_found = False
                for part in premise_parts:
                    if part.startswith("IsCentreOfCircle"):
                        match = re.match(r'IsCentreOfCircle\((\w+),(\w+)\)', part)
                        if match:
                            center, circ = match.groups()
                            if center == circle_token and circ == circle_token:
                                center_found = True
                                break

                if not center_found:
                    if circle_token not in self.circle_centers or self.circle_centers[circle_token] != circle_token:
                        return return_error(GeometricError(
                            tier=ErrorTier.TIER2_PREMISE_VIOLATION,
                            message=f"Circle center fact for {circle_token} not established",
                            details=f"Need IsCentreOfCircle({circle_token},{circle_token}) in premise"
                        ))

                return True, None
                return return_error(GeometricError(
                    tier=ErrorTier.TIER1_THEOREM_CALL_SYNTAX_VIOLATION,
                    message="these is no such version for the theorem",
                    details="these is no such version for the theorem diameter_of_circle_judgment_pass_centre"
                ))
            else:

                return return_error(GeometricError(
                    tier=ErrorTier.TIER1_THEOREM_CALL_SYNTAX_VIOLATION,
                    message="these is no such version for the theorem",
                    details="these is no such version for the theorem diameter_of_circle_judgment_pass_centre"
                ))


        elif theorem_name == "congruent_arc_judgment_chord_equal":
            version = args[0]
            if version == "1":
                if len(args) < 3:
                    return return_error(GeometricError(
                        tier=ErrorTier.TIER1_THEOREM_CALL_SYNTAX_VIOLATION,
                        message="Insufficient arguments for congruent_arc_judgment_chord_equal",
                        details="Expected: congruent_arc_judgment_chord_equal(1, arc1, arc2)"
                    ))

                arc1, arc2 = args[1].strip(), args[2].strip()

                # Check that the premise mentions both arcs
                arc1_match = re.search(r'Arc\(' + re.escape(arc1) + r'\)', premise)
                arc2_match = re.search(r'Arc\(' + re.escape(arc2) + r'\)', premise)

                if not arc1_match:
                    return return_error(GeometricError(
                        tier=ErrorTier.TIER2_PREMISE_VIOLATION,
                        message=f"Missing Arc({arc1}) in premise",
                        details="congruent_arc_judgment_chord_equal requires both arcs to be defined"
                    ))

                if not arc2_match:
                    return return_error(GeometricError(
                        tier=ErrorTier.TIER2_PREMISE_VIOLATION,
                        message=f"Missing Arc({arc2}) in premise",
                        details="congruent_arc_judgment_chord_equal requires both arcs to be defined"
                    ))

                # Extract circle and chord for first arc
                circle1 = arc1[0]
                chord1 = arc1[1:]

                # Extract circle and chord for second arc
                circle2 = arc2[0]
                chord2 = arc2[1:]

                # Check that the chords are defined as lines
                chord1_match = re.search(r'Line\(' + re.escape(chord1) + r'\)', premise)
                chord2_match = re.search(r'Line\(' + re.escape(chord2) + r'\)', premise)

                if not chord1_match:
                    return return_error(GeometricError(
                        tier=ErrorTier.TIER2_PREMISE_VIOLATION,
                        message=f"Missing Line({chord1}) in premise",
                        details="congruent_arc_judgment_chord_equal requires both chords to be defined as lines"
                    ))

                if not chord2_match:
                    return return_error(GeometricError(
                        tier=ErrorTier.TIER2_PREMISE_VIOLATION,
                        message=f"Missing Line({chord2}) in premise",
                        details="congruent_arc_judgment_chord_equal requires both chords to be defined as lines"
                    ))

                # Check for cocircularity (points of second chord lie on the first circle)
                cocircular_match = re.search(
                    r'Cocircular\(' + re.escape(circle1) + r',.*' + re.escape(chord2) + r'.*\)', premise)

                if not cocircular_match:
                    return return_error(GeometricError(
                        tier=ErrorTier.TIER2_PREMISE_VIOLATION,
                        message=f"Missing Cocircular({circle1}, ...) containing points {chord2} in premise",
                        details="congruent_arc_judgment_chord_equal requires points of the second chord to lie on the first circle"
                    ))

                # Check for equal chord lengths
                chord_equality_match = re.search(
                    r'Equal\(LengthOfLine\(' + re.escape(chord1) + r'\),LengthOfLine\(' + re.escape(chord2) + r'\)\)',
                    premise)
                if not chord_equality_match:
                    # Try reverse order too
                    chord_equality_match = re.search(
                        r'Equal\(LengthOfLine\(' + re.escape(chord2) + r'\),LengthOfLine\(' + re.escape(
                            chord1) + r'\)\)', premise)

                if not chord_equality_match:
                    return return_error(GeometricError(
                        tier=ErrorTier.TIER2_PREMISE_VIOLATION,
                        message="Missing chord length equality in premise",
                        details=f"Need Equal(LengthOfLine({chord1}),LengthOfLine({chord2})) in premise"
                    ))

                return True, None
            else:
                return return_error(GeometricError(
                    tier=ErrorTier.TIER1_THEOREM_CALL_SYNTAX_VIOLATION,
                    message="these is no such version for the theorem",
                    details="these is no such version for the theorem congruent_arc_judgment_chord_equal"
                ))


        elif theorem_name == "congruent_arc_property_measure_equal":
            version = args[0]
            if version == "1":
                if len(args) < 3:
                    return return_error(GeometricError(
                        tier=ErrorTier.TIER1_THEOREM_CALL_SYNTAX_VIOLATION,
                        message="Insufficient arguments for congruent_arc_property_measure_equal",
                        details="Expected: congruent_arc_property_measure_equal(1, arc1, arc2)"
                    ))

                arc1, arc2 = args[1].strip(), args[2].strip()

                # Check for the congruent arcs relationship in the premise
                congruent_match = re.search(r'CongruentBetweenArc\((\w+),(\w+)\)', premise)
                if not congruent_match:
                    return return_error(GeometricError(
                        tier=ErrorTier.TIER2_PREMISE_VIOLATION,
                        message="Missing congruent arcs relationship in premise",
                        details="congruent_arc_property_measure_equal requires CongruentBetweenArc(...) in premise"
                    ))

                premise_arc1, premise_arc2 = congruent_match.groups()

                # Check if the arcs in the premise match those in the function call (in any order)
                if not ((arc1 == premise_arc1 and arc2 == premise_arc2) or
                        (arc1 == premise_arc2 and arc2 == premise_arc1)):
                    return return_error(GeometricError(
                        tier=ErrorTier.TIER2_PREMISE_VIOLATION,
                        message=f"Arc mismatch: function call uses {arc1},{arc2} but premise has {premise_arc1},{premise_arc2}",
                        details="Arcs in the function call must match those in the premise"
                    ))

                # Check if the arcs are recorded as congruent in the system
                if not hasattr(self, "congruent_arcs"):
                    return return_error(GeometricError(
                        tier=ErrorTier.TIER2_PREMISE_VIOLATION,
                        message=f"Arcs {arc1} and {arc2} not proven congruent",
                        details="No congruent arcs have been established in the system"
                    ))

                canonical_arc_pair = tuple(sorted([arc1, arc2]))
                if canonical_arc_pair not in self.congruent_arcs:
                    return return_error(GeometricError(
                        tier=ErrorTier.TIER2_PREMISE_VIOLATION,
                        message=f"Arcs {arc1} and {arc2} not proven congruent",
                        details=f"Known congruent arcs: {self.congruent_arcs}"
                    ))

                return True, None
            else:
                return return_error(GeometricError(
                    tier=ErrorTier.TIER1_THEOREM_CALL_SYNTAX_VIOLATION,
                    message="these is no such version for the theorem",
                    details="these is no such version for the theorem congruent_arc_property_measure_equal"
                ))



        elif theorem_name == "mirror_congruent_triangle_judgment_aas":

            version = args[0]

            if version in {"1", "2", "3"}:  # Handle all three versions

                if len(args) < 3:
                    return return_error(GeometricError(

                        tier=ErrorTier.TIER1_THEOREM_CALL_SYNTAX_VIOLATION,

                        message="Insufficient arguments for mirror_congruent_triangle_judgment_aas",

                        details="Expected: mirror_congruent_triangle_judgment_aas(version, triangle1, triangle2)"

                    ))

                tri1, tri2 = args[1].strip(), args[2].strip()

                # Check for polygon definitions

                polygon_matches = re.findall(r'Polygon\((\w+)\)', premise)

                if len(polygon_matches) < 2:
                    return return_error(GeometricError(

                        tier=ErrorTier.TIER2_PREMISE_VIOLATION,

                        message="Missing polygon definitions in premise",

                        details="mirror_congruent_triangle_judgment_aas requires both triangles to be defined"

                    ))

                # Check for angle equalities

                angle_equalities = re.findall(r'Equal\(MeasureOfAngle\((\w+)\),MeasureOfAngle\((\w+)\)\)', premise)

                if len(angle_equalities) < 2:
                    return return_error(GeometricError(

                        tier=ErrorTier.TIER2_PREMISE_VIOLATION,

                        message="Insufficient angle equalities in premise",

                        details="mirror_congruent_triangle_judgment_aas requires at least 2 equal angle pairs"

                    ))

                # Check for side equality

                side_equality = re.search(r'Equal\(LengthOfLine\((\w+)\),LengthOfLine\((\w+)\)\)', premise)

                if not side_equality:
                    return return_error(GeometricError(

                        tier=ErrorTier.TIER2_PREMISE_VIOLATION,

                        message="Missing side equality in premise",

                        details="mirror_congruent_triangle_judgment_aas requires one equal side pair"

                    ))

                return True, None

            else:

                return return_error(GeometricError(
                    tier=ErrorTier.TIER1_THEOREM_CALL_SYNTAX_VIOLATION,
                    message="these is no such version for the theorem",
                    details="these is no such version for the theorem mirror_congruent_triangle_judgment_aas"
                ))



        elif theorem_name == "mirror_congruent_triangle_judgment_sas":
            version = args[0]
            if version == "1":
                if len(args) < 3:
                    return return_error(GeometricError(
                        tier=ErrorTier.TIER1_THEOREM_CALL_SYNTAX_VIOLATION,
                        message="Insufficient arguments for mirror_congruent_triangle_judgment_sas",
                        details="Expected: mirror_congruent_triangle_judgment_sas(1, triangle1, triangle2)"
                    ))

                # Check for polygon definitions and side/angle equalities in premise
                polygon_count = premise.count("Polygon(")
                if polygon_count < 2:
                    return return_error(GeometricError(
                        tier=ErrorTier.TIER2_PREMISE_VIOLATION,
                        message="Missing polygon definitions in premise",
                        details="mirror_congruent_triangle_judgment_sas requires both triangles to be defined"
                    ))

                # Check for side equalities
                side_equalities = len(re.findall(r'Equal\(LengthOfLine\((\w+)\),LengthOfLine\((\w+)\)\)', premise))
                if side_equalities < 2:  # Need at least 2 side equalities for SAS
                    return return_error(GeometricError(
                        tier=ErrorTier.TIER2_PREMISE_VIOLATION,
                        message="Insufficient side equalities in premise",
                        details="mirror_congruent_triangle_judgment_sas requires at least 2 equal sides"
                    ))

                # Check for angle equality
                angle_equality = len(re.findall(r'Equal\(MeasureOfAngle\((\w+)\),MeasureOfAngle\((\w+)\)\)', premise))
                if angle_equality < 1:  # Need at least 1 angle equality for SAS
                    return return_error(GeometricError(
                        tier=ErrorTier.TIER2_PREMISE_VIOLATION,
                        message="Missing angle equality in premise",
                        details="mirror_congruent_triangle_judgment_sas requires at least 1 equal angle"
                    ))

                return True, None
            else:
                return return_error(GeometricError(
                    tier=ErrorTier.TIER1_THEOREM_CALL_SYNTAX_VIOLATION,
                    message="these is no such version for the theorem",
                    details="these is no such version for the theorem mirror_congruent_triangle_judgment_sas"
                ))


        elif theorem_name == "mirror_congruent_triangle_property_angle_equal":
            version = args[0]
            if version == "1":
                if len(args) < 3:
                    return return_error(GeometricError(
                        tier=ErrorTier.TIER1_THEOREM_CALL_SYNTAX_VIOLATION,
                        message="Insufficient arguments for mirror_congruent_triangle_property_angle_equal",
                        details="Expected: mirror_congruent_triangle_property_angle_equal(1, triangle1, triangle2)"
                    ))

                tri1, tri2 = args[1].strip(), args[2].strip()

                # Check for mirror congruence in premise
                mirror_congruent_match = re.search(r'MirrorCongruentBetweenTriangle\((\w+),(\w+)\)', premise)
                if not mirror_congruent_match:
                    return return_error(GeometricError(
                        tier=ErrorTier.TIER2_PREMISE_VIOLATION,
                        message="Missing MirrorCongruentBetweenTriangle(...) in premise",
                        details="mirror_congruent_triangle_property_angle_equal requires mirror congruent triangles"
                    ))

                premise_tri1, premise_tri2 = mirror_congruent_match.groups()

                # Create canonical representations
                theorem_pair = self.canonicalize_mirror_congruent_triangle_pair(tri1, tri2)
                premise_pair = self.canonicalize_mirror_congruent_triangle_pair(premise_tri1, premise_tri2)

                # Check triangles match using canonical form
                if theorem_pair != premise_pair:
                    return return_error(GeometricError(
                        tier=ErrorTier.TIER2_PREMISE_VIOLATION,
                        message=f"Triangles in premise ({premise_tri1}, {premise_tri2}) don't match those in theorem call ({tri1}, {tri2})",
                        details="Triangles must match between premise and theorem call"
                    ))

                canonical_pair = self.canonicalize_mirror_congruent_triangle_pair(tri1, tri2)
                if canonical_pair not in self.mirror_congruent_triangles:
                    return return_error(GeometricError(
                        tier=ErrorTier.TIER2_PREMISE_VIOLATION,
                        message=f"Triangles {tri1} and {tri2} not proven mirror congruent",
                        details="Required for mirror_congruent_triangle_property_angle_equal"
                    ))

                return True, None
            else:
                return return_error(GeometricError(
                    tier=ErrorTier.TIER1_THEOREM_CALL_SYNTAX_VIOLATION,
                    message="these is no such version for the theorem",
                    details="these is no such version for the theorem mirror_congruent_triangle_property_angle_equal"
                ))


        elif theorem_name == "parallel_judgment_par_par":
            version = args[0]
            if version == "1":
                if len(args) < 4:
                    return return_error(GeometricError(
                        tier=ErrorTier.TIER1_THEOREM_CALL_SYNTAX_VIOLATION,
                        message="Insufficient arguments for parallel_judgment_par_par",
                        details="Expected: parallel_judgment_par_par(1, line1, middle_line, line2)"
                    ))

                line1, middle_line, line2 = args[1].strip(), args[2].strip(), args[3].strip()

                # Check that the premise contains both parallel relationships
                if "ParallelBetweenLine" not in premise:
                    return return_error(GeometricError(
                        tier=ErrorTier.TIER2_PREMISE_VIOLATION,
                        message="Missing ParallelBetweenLine in premise",
                        details="parallel_judgment_par_par requires two parallel line relationships"
                    ))

                # Check for the specific parallel relationships in the premise
                parallel1_found = False
                parallel2_found = False

                for pattern in [
                    f"ParallelBetweenLine({line1},{middle_line})",
                    f"ParallelBetweenLine({middle_line},{line1})"
                ]:
                    if pattern in premise:
                        parallel1_found = True
                        break

                for pattern in [
                    f"ParallelBetweenLine({middle_line},{line2})",
                    f"ParallelBetweenLine({line2},{middle_line})"
                ]:
                    if pattern in premise:
                        parallel2_found = True
                        break

                if not parallel1_found:
                    return return_error(GeometricError(
                        tier=ErrorTier.TIER2_PREMISE_VIOLATION,
                        message=f"Missing parallel relationship between {line1} and {middle_line} in premise",
                        details="Required for parallel_judgment_par_par"
                    ))

                if not parallel2_found:
                    return return_error(GeometricError(
                        tier=ErrorTier.TIER2_PREMISE_VIOLATION,
                        message=f"Missing parallel relationship between {middle_line} and {line2} in premise",
                        details="Required for parallel_judgment_par_par"
                    ))

                return True, None
            else:
                return return_error(GeometricError(
                    tier=ErrorTier.TIER1_THEOREM_CALL_SYNTAX_VIOLATION,
                    message="these is no such version for the theorem",
                    details="these is no such version for the theorem parallel_judgment_par_par"
                ))




        elif theorem_name == "mirror_congruent_triangle_property_line_equal":

            version = args[0]

            if version == "1":

                if len(args) < 3:
                    return return_error(GeometricError(

                        tier=ErrorTier.TIER1_THEOREM_CALL_SYNTAX_VIOLATION,

                        message="Insufficient arguments for mirror_congruent_triangle_property_line_equal",

                        details="Expected: mirror_congruent_triangle_property_line_equal(1, triangle1, triangle2)"

                    ))

                tri1, tri2 = args[1].strip(), args[2].strip()

                # Check for mirror congruence in premise

                mirror_congruent_match = re.search(r'MirrorCongruentBetweenTriangle\((\w+),(\w+)\)', premise)

                if not mirror_congruent_match:
                    return return_error(GeometricError(

                        tier=ErrorTier.TIER2_PREMISE_VIOLATION,

                        message="Missing MirrorCongruentBetweenTriangle(...) in premise",

                        details="mirror_congruent_triangle_property_line_equal requires mirror congruent triangles"

                    ))

                premise_tri1, premise_tri2 = mirror_congruent_match.groups()

                # Create canonical representations

                theorem_pair = self.canonicalize_mirror_congruent_triangle_pair(tri1, tri2)

                premise_pair = self.canonicalize_mirror_congruent_triangle_pair(premise_tri1, premise_tri2)

                # Check triangles match using canonical form

                if theorem_pair != premise_pair:
                    return return_error(GeometricError(

                        tier=ErrorTier.TIER2_PREMISE_VIOLATION,

                        message=f"Triangles in premise ({premise_tri1}, {premise_tri2}) don't match those in theorem call ({tri1}, {tri2})",

                        details="Triangles must match between premise and theorem call"

                    ))

                canonical_pair = self.canonicalize_mirror_congruent_triangle_pair(tri1, tri2)

                if canonical_pair not in self.mirror_congruent_triangles:
                    return return_error(GeometricError(

                        tier=ErrorTier.TIER2_PREMISE_VIOLATION,

                        message=f"Triangles {tri1} and {tri2} not proven mirror congruent",

                        details="Required for mirror_congruent_triangle_property_line_equal"

                    ))

                return True, None
            else:
                return return_error(GeometricError(
                    tier=ErrorTier.TIER1_THEOREM_CALL_SYNTAX_VIOLATION,
                    message="these is no such version for the theorem",
                    details="these is no such version for the theorem mirror_congruent_triangle_property_line_equal"
                ))



        elif theorem_name == "midsegment_of_triangle_judgment_midpoint":

            version = args[0]

            if version == "1":

                if len(args) < 3:
                    return return_error(GeometricError(

                        tier=ErrorTier.TIER1_THEOREM_CALL_SYNTAX_VIOLATION,

                        message="Insufficient arguments for midsegment_of_triangle_judgment_midpoint",

                        details="Expected: midsegment_of_triangle_judgment_midpoint(1, segment, triangle)"

                    ))

                # Simple check for polygon definition and length equalities

                if "Polygon" not in premise or "Equal(LengthOfLine" not in premise:
                    return return_error(GeometricError(

                        tier=ErrorTier.TIER2_PREMISE_VIOLATION,

                        message="Missing required components in premise",

                        details="midsegment_of_triangle_judgment_midpoint requires a polygon and length equalities"

                    ))

                return True, None
            else:
                return return_error(GeometricError(
                    tier=ErrorTier.TIER1_THEOREM_CALL_SYNTAX_VIOLATION,
                    message="these is no such version for the theorem",
                    details="these is no such version for the theorem midsegment_of_triangle_judgment_midpoint"
                ))



        elif theorem_name == "midsegment_of_triangle_property_length":

            version = args[0]

            if version == "1":

                if len(args) < 3:
                    return return_error(GeometricError(

                        tier=ErrorTier.TIER1_THEOREM_CALL_SYNTAX_VIOLATION,

                        message="Insufficient arguments for midsegment_of_triangle_property_length",

                        details="Expected: midsegment_of_triangle_property_length(1, segment, triangle)"

                    ))

                segment, triangle = args[1].strip(), args[2].strip()

                # Look for the midsegment fact in the premise directly - don't rely on self.midsegments

                midsegment_match = re.search(
                    r'IsMidsegmentOfTriangle\(' + re.escape(segment) + ',' + re.escape(triangle) + r'\)', premise)

                if not midsegment_match:
                    return return_error(GeometricError(

                        tier=ErrorTier.TIER2_PREMISE_VIOLATION,

                        message=f"Missing IsMidsegmentOfTriangle({segment},{triangle}) in premise",

                        details="midsegment_of_triangle_property_length requires the segment to be established as a midsegment"

                    ))

                return True, None
            else:
                return return_error(GeometricError(
                    tier=ErrorTier.TIER1_THEOREM_CALL_SYNTAX_VIOLATION,
                    message="these is no such version for the theorem",
                    details="these is no such version for the theorem midsegment_of_triangle_property_length"
                ))


        elif theorem_name == "congruent_triangle_property_angle_equal":
            version = args[0]
            if version != "1":  # Updated to include version "2"
                return return_error(GeometricError(
                    tier=ErrorTier.TIER1_THEOREM_CALL_SYNTAX_VIOLATION,
                    message="these is no such version for the theorem",
                    details="these is no such version for the theorem congruent_triangle_property_angle_equal"
                ))

            if version == "1":
                if len(args) < 3:
                    return return_error(GeometricError(
                        tier=ErrorTier.TIER1_THEOREM_CALL_SYNTAX_VIOLATION,
                        message="Insufficient arguments for congruent_triangle_property_angle_equal",
                        details="Expected: congruent_triangle_property_angle_equal(1, triangle1, triangle2)"
                    ))

                tri1, tri2 = args[1].strip(), args[2].strip()

                # Check for congruence in premise
                congruent_match = re.search(r'CongruentBetweenTriangle\((\w+),(\w+)\)', premise)
                if not congruent_match:
                    return return_error(GeometricError(
                        tier=ErrorTier.TIER2_PREMISE_VIOLATION,
                        message="Missing CongruentBetweenTriangle(...) in premise",
                        details="congruent_triangle_property_angle_equal requires congruent triangles"
                    ))

                premise_tri1, premise_tri2 = congruent_match.groups()

                # Create canonical representations for theorem triangles and premise triangles
                theorem_pair = self.canonicalize_congruent_triangle_pair(tri1, tri2)
                premise_pair = self.canonicalize_congruent_triangle_pair(premise_tri1, premise_tri2)

                # Check if triangles in premise match those in theorem call using canonical form
                if theorem_pair != premise_pair:
                    return return_error(GeometricError(
                        tier=ErrorTier.TIER2_PREMISE_VIOLATION,
                        message=f"Triangles in premise ({premise_tri1}, {premise_tri2}) don't match those in theorem call ({tri1}, {tri2})",
                        details="Triangles must match between premise and theorem call"
                    ))

                # Check if these triangles are recorded as congruent using canonical form
                canonical_pair = self.canonicalize_congruent_triangle_pair(tri1, tri2)
                if canonical_pair not in self.congruent_triangles:
                    return return_error(GeometricError(
                        tier=ErrorTier.TIER2_PREMISE_VIOLATION,
                        message=f"Triangles {tri1} and {tri2} not proven congruent",
                        details="Required for congruent_triangle_property_angle_equal"
                    ))

                return True, None

        elif theorem_name == "congruent_triangle_property_line_equal":

            version = args[0]
            if version != "1":  # Updated to include version "2"
                return return_error(GeometricError(
                    tier=ErrorTier.TIER1_THEOREM_CALL_SYNTAX_VIOLATION,
                    message="these is no such version for the theorem",
                    details="these is no such version for the theorem congruent_triangle_property_line_equal"
                ))

            if version == "1":

                if len(args) < 3:
                    return return_error(GeometricError(

                        tier=ErrorTier.TIER1_THEOREM_CALL_SYNTAX_VIOLATION,

                        message="Insufficient arguments for congruent_triangle_property_line_equal",

                        details="Expected: congruent_triangle_property_line_equal(1, triangle1, triangle2)"

                    ))

                tri1, tri2 = args[1].strip(), args[2].strip()

                # Check for congruence in premise

                congruent_match = re.search(r'CongruentBetweenTriangle\((\w+),(\w+)\)', premise)

                if not congruent_match:
                    return return_error(GeometricError(

                        tier=ErrorTier.TIER2_PREMISE_VIOLATION,

                        message="Missing CongruentBetweenTriangle(...) in premise",

                        details="congruent_triangle_property_line_equal requires congruent triangles"

                    ))

                premise_tri1, premise_tri2 = congruent_match.groups()

                # Create canonical representations for theorem triangles and premise triangles

                theorem_pair = self.canonicalize_congruent_triangle_pair(tri1, tri2)

                premise_pair = self.canonicalize_congruent_triangle_pair(premise_tri1, premise_tri2)

                # Check if triangles in premise match those in theorem call using canonical form

                if theorem_pair != premise_pair:
                    return return_error(GeometricError(

                        tier=ErrorTier.TIER2_PREMISE_VIOLATION,

                        message=f"Triangles in premise ({premise_tri1}, {premise_tri2}) don't match those in theorem call ({tri1}, {tri2})",

                        details="Triangles must match between premise and theorem call"

                    ))

                # Check if these triangles are recorded as congruent using canonical form

                canonical_pair = self.canonicalize_congruent_triangle_pair(tri1, tri2)

                if canonical_pair not in self.congruent_triangles:
                    return return_error(GeometricError(

                        tier=ErrorTier.TIER2_PREMISE_VIOLATION,

                        message=f"Triangles {tri1} and {tri2} not proven congruent",

                        details="Required for congruent_triangle_property_line_equal"

                    ))

                return True, None


        elif theorem_name == "median_of_triangle_judgment":
            version = args[0]

            if version != "1":  # Updated to include version "2"
                return return_error(GeometricError(
                    tier=ErrorTier.TIER1_THEOREM_CALL_SYNTAX_VIOLATION,
                    message="these is no such version for the theorem",
                    details="these is no such version for the theorem median_of_triangle_judgment"
                ))

            if version == "1":
                if len(args) < 3:
                    return return_error(GeometricError(
                        tier=ErrorTier.TIER1_THEOREM_CALL_SYNTAX_VIOLATION,
                        message="Missing arguments for median_of_triangle_judgment",
                        details="Expected median_of_triangle_judgment(1, median_line, triangle)"
                    ))

                median_line = args[1].strip()  # e.g., "EM"
                triangle = args[2].strip()  # e.g., "EBC"

                # Check if the triangle exists in our polygon database
                # if self.normalize_triangle(triangle) not in self.polygons:
                #     return return_error(GeometricError(
                #         tier=ErrorTier.TIER2_PREMISE_VIOLATION,
                #         message=f"Triangle {triangle} is not defined in the geometric data",
                #         details=f"Known polygons: {self.polygons}"
                #     ))

                # Check if the line exists
                # line_match = re.search(r'Line\((\w+)\)', premise)
                # if not line_match or line_match.group(1) != median_line:
                #     return return_error(GeometricError(
                #         tier=ErrorTier.TIER2_PREMISE_VIOLATION,
                #         message=f"Line {median_line} is not defined in the premise",
                #         details="A median must be a defined line"
                #     ))

                # Extract the opposite side vertices (not connected to median's vertex)
                # For a median from E to M in triangle EBC, we need to check if M is on BC
                endpoints = median_line[0] + median_line[1]  # "EM"
                median_vertex = median_line[0]  # "E"
                median_foot = median_line[1]  # "M"

                # The other two vertices should be the remaining ones in the triangle
                other_vertices = [v for v in triangle if v != median_vertex]  # ["B", "C"]

                # Check if the collinearity fact exists for the median foot and the opposite side
                collinear_match = re.search(r'Collinear\((\w+)\)', premise)
                if not collinear_match:
                    return return_error(GeometricError(
                        tier=ErrorTier.TIER2_PREMISE_VIOLATION,
                        message="Missing collinearity in premise",
                        details="A median requires collinearity of the foot and the opposite side"
                    ))

                collinear_points = collinear_match.group(1)  # "BMC"

                # Check that the median foot and the other vertices are collinear
                if not (median_foot in collinear_points and all(v in collinear_points for v in other_vertices)):
                    return return_error(GeometricError(
                        tier=ErrorTier.TIER2_PREMISE_VIOLATION,
                        message="Incorrect collinearity for median judgment",
                        details=f"Need collinearity between median foot {median_foot} and opposite vertices {other_vertices}"
                    ))

                # Check for the length equality fact
                length_eq_match = re.search(r'Equal\(LengthOfLine\((\w+)\),LengthOfLine\((\w+)\)\)', premise)
                if not length_eq_match:
                    return return_error(GeometricError(
                        tier=ErrorTier.TIER2_PREMISE_VIOLATION,
                        message="Missing length equality in premise",
                        details="A median requires equal lengths on both sides of the foot"
                    ))

                side1, side2 = length_eq_match.groups()  # "BM", "CM"

                # Ensure this equality is for the segments formed by the median foot
                expected_segments = [median_foot + other_vertices[0], other_vertices[0] + median_foot,
                                     median_foot + other_vertices[1], other_vertices[1] + median_foot]

                if not ((side1 in expected_segments) and (side2 in expected_segments)):
                    return return_error(GeometricError(
                        tier=ErrorTier.TIER2_PREMISE_VIOLATION,
                        message="Incorrect length equality for median judgment",
                        details=f"The lengths must be for segments connecting the median foot to the opposite vertices"
                    ))

                return True, None


        # In the validate_theorem_premises method
        elif theorem_name == "right_triangle_property_length_of_median":
            version = args[0]
            if version != "1":  # Updated to include version "2"
                return return_error(GeometricError(
                    tier=ErrorTier.TIER1_THEOREM_CALL_SYNTAX_VIOLATION,
                    message="these is no such version for the theorem",
                    details="these is no such version for the theorem parallelogram_property_diagonal_bisection"
                ))
            if version == "1":
                if len(args) < 3:
                    return return_error(GeometricError(
                        tier=ErrorTier.TIER1_THEOREM_CALL_SYNTAX_VIOLATION,
                        message="Missing arguments for right_triangle_property_length_of_median",
                        details="Expected right_triangle_property_length_of_median(1, triangle, median_endpoint)"
                    ))

                triangle = args[1].strip()  # e.g., "CEB"
                median_endpoint = args[2].strip()  # e.g., "M"

                # Check if the triangle is a right triangle
                if self.normalize_triangle(triangle) not in self.right_triangles:
                    return return_error(GeometricError(
                        tier=ErrorTier.TIER2_PREMISE_VIOLATION,
                        message=f"Triangle {triangle} is not proven to be a right triangle",
                        details=f"Known right triangles: {self.right_triangles}"
                    ))

                # Check if the median has been established
                # We need to reconstruct the median line and find its start point
                # Since we only have the endpoint M, we need to find the starting vertex

                # Find the IsMedianOfTriangle fact in self.medians
                median_found = False
                median_line = ""
                median_triangle = ""

                for median, tri in self.medians:
                    if median_endpoint in median and self.normalize_triangle(tri) == self.normalize_triangle(triangle):
                        median_found = True
                        median_line = median
                        median_triangle = tri
                        break

                if not median_found:
                    return return_error(GeometricError(
                        tier=ErrorTier.TIER2_PREMISE_VIOLATION,
                        message=f"Median ending at {median_endpoint} for triangle {triangle} not established",
                        details="Need to first establish the median using median_of_triangle_judgment"
                    ))

                # Ensure that the median is to the hypotenuse of the right triangle
                # In a right triangle, the hypotenuse is opposite to the right angle

                # Find which vertex has the right angle
                right_angle_vertex = None
                for i in range(3):
                    v1 = triangle[i]
                    v2 = triangle[(i + 1) % 3]
                    v3 = triangle[(i + 2) % 3]
                    angle = self.normalize_angle_name(v1 + v2 + v3)
                    angle_var = self.angles.get(f"angle_{angle}")

                    if angle_var is not None:
                        # Check if this angle is constrained to be 90 degrees
                        temp_solver = Solver()
                        for c in self.solver.assertions():
                            temp_solver.add(c)
                        temp_solver.add(angle_var != 90)
                        if temp_solver.check() == unsat:
                            right_angle_vertex = v2
                            break

                if right_angle_vertex is None:
                    return return_error(GeometricError(
                        tier=ErrorTier.TIER2_PREMISE_VIOLATION,
                        message=f"Could not determine the right angle in triangle {triangle}",
                        details="A right triangle must have one angle of 90 degrees"
                    ))

                # The two vertices that are not the right angle vertex form the hypotenuse
                hypotenuse_vertices = [v for v in triangle if v != right_angle_vertex]

                # Check that the median is from the right angle to the midpoint of the hypotenuse
                median_start = median_line[0]

                if median_start != right_angle_vertex:
                    return return_error(GeometricError(
                        tier=ErrorTier.TIER2_PREMISE_VIOLATION,
                        message=f"Median {median_line} is not from the right angle to the hypotenuse",
                        details=f"The median must start at the right angle vertex {right_angle_vertex}"
                    ))

                return True, None


        # In the validate_theorem_premises method
        elif theorem_name == "median_of_triangle_judgment":
            version = args[0]
            if version == "1":
                if len(args) < 3:
                    return return_error(GeometricError(
                        tier=ErrorTier.TIER1_THEOREM_CALL_SYNTAX_VIOLATION,
                        message="Missing arguments for median_of_triangle_judgment",
                        details="Expected median_of_triangle_judgment(1, median_line, triangle)"
                    ))

                median_line = args[1].strip()  # e.g., "EM"
                triangle = args[2].strip()  # e.g., "EBC"

                # Check if the triangle exists in our polygon database
                if self.normalize_triangle(triangle) not in self.polygons:
                    return return_error(GeometricError(
                        tier=ErrorTier.TIER2_PREMISE_VIOLATION,
                        message=f"Triangle {triangle} is not defined in the geometric data",
                        details=f"Known polygons: {self.polygons}"
                    ))

                # Extract the median vertex and foot
                median_vertex = median_line[0]  # "E"
                median_foot = median_line[1]  # "M"

                # The other two vertices should be the remaining ones in the triangle
                other_vertices = [v for v in triangle if v != median_vertex]  # ["B", "C"]

                # Check if there is a collinearity fact containing the median foot and the opposite vertices
                collinear_found = False
                for fact in self.collinear_facts:
                    fact_str = ''.join(fact)
                    if median_foot in fact_str and all(v in fact_str for v in other_vertices):
                        collinear_found = True
                        break

                if not collinear_found:
                    return return_error(GeometricError(
                        tier=ErrorTier.TIER2_PREMISE_VIOLATION,
                        message="Missing collinearity for median judgment",
                        details=f"Need collinearity between median foot {median_foot} and opposite vertices {other_vertices}"
                    ))

                # Check if the lengths of the segments are equal
                segment1 = median_foot + other_vertices[0]  # "MB"
                segment2 = median_foot + other_vertices[1]  # "MC"

                normalized_segment1 = self.normalize_line_name(segment1)
                normalized_segment2 = self.normalize_line_name(segment2)

                # Check if the lengths are forced to be equal by the solver
                length1_var = self.add_length(normalized_segment1[0], normalized_segment1[1])
                length2_var = self.add_length(normalized_segment2[0], normalized_segment2[1])

                # Create a temporary solver with all current constraints
                temp_solver = Solver()
                for c in self.solver.assertions():
                    temp_solver.add(c)

                # If adding the inequality makes the system unsat, then they are equal
                temp_solver.add(length1_var != length2_var)
                if temp_solver.check() != unsat:
                    return return_error(GeometricError(
                        tier=ErrorTier.TIER2_PREMISE_VIOLATION,
                        message="Equal segment lengths not established for median",
                        details=f"Segments {normalized_segment1} and {normalized_segment2} must be equal"
                    ))

                return True, None
            else:
                return return_error(GeometricError(
                    tier=ErrorTier.TIER1_THEOREM_CALL_SYNTAX_VIOLATION,
                    message="these is no such version for the theorem",
                    details="these is no such version for the theorem median_of_triangle_judgment"
                ))


        elif theorem_name == "incenter_of_triangle_judgment_intersection":
            version = args[0]
            if version != "1":  # Updated to include version "2"
                return return_error(GeometricError(
                    tier=ErrorTier.TIER1_THEOREM_CALL_SYNTAX_VIOLATION,
                    message="these is no such version for the theorem",
                    details="these is no such version for the theorem incenter_of_triangle_judgment_intersection"
                ))

            if version == "1":
                if len(args) < 3:
                    return return_error(GeometricError(
                        tier=ErrorTier.TIER1_THEOREM_CALL_SYNTAX_VIOLATION,
                        message="Missing arguments for incenter_of_triangle_judgment_intersection",
                        details="Expected incenter_of_triangle_judgment_intersection(1, point, triangle)"
                    ))

                point = args[1].strip()  # e.g., "O"
                triangle = args[2].strip()  # e.g., "ABC"

                # Check that polygon exists
                polygon_match = re.search(r'Polygon\((\w+)\)', premise)
                if not polygon_match or polygon_match.group(1) != triangle:
                    return return_error(GeometricError(
                        tier=ErrorTier.TIER2_PREMISE_VIOLATION,
                        message=f"Missing or incorrect polygon in premise",
                        details=f"Expected Polygon({triangle})"
                    ))

                # Check for angle bisector facts
                bisector_pattern = r'IsBisectorOfAngle\((\w+),(\w+)\)'
                bisector_matches = re.findall(bisector_pattern, premise)

                if len(bisector_matches) < 2:
                    return return_error(GeometricError(
                        tier=ErrorTier.TIER2_PREMISE_VIOLATION,
                        message="Missing angle bisector facts",
                        details="Need at least two angle bisectors to determine incenter"
                    ))

                # Verify each angle bisector
                for line, angle in bisector_matches:
                    # Check if the line contains the point O
                    if point not in line:
                        return return_error(GeometricError(
                            tier=ErrorTier.TIER2_PREMISE_VIOLATION,
                            message=f"Angle bisector {line} does not contain point {point}",
                            details="Angle bisector must contain the incenter"
                        ))

                return True, None


        elif theorem_name == "vertical_angle":
            version = args[0]
            if version == "1":
                if len(args) < 3:
                    return return_error(GeometricError(
                        tier=ErrorTier.TIER1_THEOREM_CALL_SYNTAX_VIOLATION,
                        message="Insufficient arguments for vertical_angle",
                        details="Expected vertical_angle(1, angle1, angle2)"
                    ))

                angle1 = args[1].strip()  # e.g., "DEB"
                angle2 = args[2].strip()  # e.g., "CEA"

                # Parse the premise parts
                premise_parts = premise.split('&')

                # Check for at least 4 parts (2 collinear facts and 2 angle facts)
                if len(premise_parts) < 4:
                    return return_error(GeometricError(
                        tier=ErrorTier.TIER2_PREMISE_VIOLATION,
                        message="Incomplete premise for vertical_angle",
                        details="Expected 2 collinear facts and 2 angle facts"
                    ))

                # Extract and verify collinear facts
                collinear_parts = [p for p in premise_parts if p.startswith("Collinear")]
                if len(collinear_parts) < 2:
                    return return_error(GeometricError(
                        tier=ErrorTier.TIER2_PREMISE_VIOLATION,
                        message="Missing collinear facts in premise",
                        details="Vertical angle theorem requires two collinear facts"
                    ))

                collinear_matches = [re.match(r'Collinear\((\w+)\)', part) for part in collinear_parts]
                if not all(collinear_matches):
                    return return_error(GeometricError(
                        tier=ErrorTier.TIER2_PREMISE_VIOLATION,
                        message="Invalid collinear fact format",
                        details="Expected Collinear(XXX)"
                    ))

                collinear_points = [m.group(1) for m in collinear_matches if m]

                # Verify each collinear fact exists in the system
                for points in collinear_points:
                    normalized = self.normalize_collinear_points(points)
                    if not any(self.normalize_collinear_points(''.join(fact)) == normalized
                               for fact in self.collinear_facts):
                        return return_error(GeometricError(
                            tier=ErrorTier.TIER2_PREMISE_VIOLATION,
                            message=f"Collinear fact for {points} not established",
                            details=f"Known collinear facts: {[''.join(p) for p in self.collinear_facts]}"
                        ))

                # Check that the collinear lines intersect at the angle vertex
                # For vertical angles, both angles must share the same vertex (middle point)
                if angle1[1] != angle2[1]:
                    return return_error(GeometricError(
                        tier=ErrorTier.TIER2_PREMISE_VIOLATION,
                        message="Angles do not share a common vertex",
                        details=f"Angles {angle1} and {angle2} must have the same middle point for vertical angles"
                    ))

                # Common vertex (intersection point)
                common_vertex = angle1[1]

                # Verify common vertex is in both collinear lines
                if not all(common_vertex in points for points in collinear_points):
                    return return_error(GeometricError(
                        tier=ErrorTier.TIER2_PREMISE_VIOLATION,
                        message=f"Vertex {common_vertex} not in both collinear lines",
                        details="The angle vertex must be the intersection point of the lines"
                    ))

                # Verify angle facts
                angle_parts = [p for p in premise_parts if p.startswith("Angle")]
                if len(angle_parts) < 2:
                    return return_error(GeometricError(
                        tier=ErrorTier.TIER2_PREMISE_VIOLATION,
                        message="Missing angle facts in premise",
                        details="Vertical angle theorem requires two angle facts"
                    ))

                # Check that the specified angles are in the angle parts
                if not any(p == f"Angle({angle1})" for p in angle_parts):
                    return return_error(GeometricError(
                        tier=ErrorTier.TIER2_PREMISE_VIOLATION,
                        message=f"Angle fact for {angle1} missing in premise",
                        details=f"Expected Angle({angle1})"
                    ))

                if not any(p == f"Angle({angle2})" for p in angle_parts):
                    return return_error(GeometricError(
                        tier=ErrorTier.TIER2_PREMISE_VIOLATION,
                        message=f"Angle fact for {angle2} missing in premise",
                        details=f"Expected Angle({angle2})"
                    ))

                # All checks passed
                return True, None
            else:
                return return_error(GeometricError(
                    tier=ErrorTier.TIER1_THEOREM_CALL_SYNTAX_VIOLATION,
                    message="these is no such version for the theorem",
                    details="these is no such version for the theorem vertical_angle"
                ))




        elif theorem_name == "isosceles_triangle_judgment_angle_equal":
            version = args[0]
            if version == "1":
                if len(args) < 2:
                    return return_error(GeometricError(
                        tier=ErrorTier.TIER1_THEOREM_CALL_SYNTAX_VIOLATION,
                        message="Missing triangle argument for isosceles_triangle_judgment_angle_equal",
                        details="Expected isosceles_triangle_judgment_angle_equal(1, triangle)"
                    ))

                triangle = args[1].strip()  # e.g., "ABE"

                # Parse premise parts
                premise_parts = premise.split('&')

                # First check if the polygon exists in our stored polygons
                polygon_part = premise_parts[0].strip()
                polygon_match = re.match(r'Polygon\((\w+)\)', polygon_part)

                if not polygon_match:
                    return return_error(GeometricError(
                        tier=ErrorTier.TIER2_PREMISE_VIOLATION,
                        message="Missing or invalid polygon fact in premise",
                        details="Expected Polygon(...) in premise"
                    ))

                polygon_name = polygon_match.group(1)
                if polygon_name != triangle:
                    return return_error(GeometricError(
                        tier=ErrorTier.TIER2_PREMISE_VIOLATION,
                        message=f"Polygon in premise ({polygon_name}) doesn't match triangle in theorem call ({triangle})",
                        details="Polygon and triangle argument must match"
                    ))

                # Check if this polygon is defined in our system
                norm_triangle = self.normalize_triangle(triangle)
                if norm_triangle not in self.polygons:
                    return return_error(GeometricError(
                        tier=ErrorTier.TIER2_PREMISE_VIOLATION,
                        message=f"Polygon {triangle} is not defined in the system",
                        details="The construction data did not define this polygon"
                    ))

                # Check for the angle equality in the premise
                if len(premise_parts) < 2:
                    return return_error(GeometricError(
                        tier=ErrorTier.TIER2_PREMISE_VIOLATION,
                        message="Missing angle equality in premise",
                        details="Expected Equal(MeasureOfAngle(...),MeasureOfAngle(...)) in premise"
                    ))

                angle_equality = premise_parts[1].strip()
                angle_match = re.match(r'Equal\(MeasureOfAngle\((\w{3})\),\s*MeasureOfAngle\((\w{3})\)\)',
                                       angle_equality)

                if not angle_match:
                    return return_error(GeometricError(
                        tier=ErrorTier.TIER2_PREMISE_VIOLATION,
                        message="Invalid angle equality format in premise",
                        details="Expected Equal(MeasureOfAngle(XXX),MeasureOfAngle(YYY)) format"
                    ))

                angle1, angle2 = angle_match.groups()

                # Verify that this angle equality actually holds in our current constraints
                if not self.check_angle_equality(angle1, angle2):
                    return return_error(GeometricError(
                        tier=ErrorTier.TIER2_PREMISE_VIOLATION,
                        message=f"Angles {angle1} and {angle2} are not proven equal in the system",
                        details="The current constraints don't force these angles to be equal"
                    ))

                return True, None
            else:
                return return_error(GeometricError(
                    tier=ErrorTier.TIER1_THEOREM_CALL_SYNTAX_VIOLATION,
                    message="these is no such version for the theorem",
                    details="these is no such version for the theorem isosceles_triangle_judgment_angle_equal"
                ))


        elif theorem_name == "parallelogram_judgment_parallel_and_parallel":
            version = args[0]
            if version == "1":
                if len(args) < 2:
                    return return_error(GeometricError(
                        tier=ErrorTier.TIER1_THEOREM_CALL_SYNTAX_VIOLATION,
                        message="Missing quadrilateral name for parallelogram_judgment_parallel_and_parallel",
                        details="Expected parallelogram_judgment_parallel_and_parallel(1, quadrilateral)"
                    ))

                quad_name = args[1].strip()  # e.g., "BCDF"

                # Parse the premise parts
                premise_parts = premise.split('&')

                # First check if the polygon exists in our system
                polygon_part = premise_parts[0].strip() if premise_parts else ""
                polygon_match = re.match(r'Polygon\((\w+)\)', polygon_part)

                if not polygon_match:
                    return return_error(GeometricError(
                        tier=ErrorTier.TIER2_PREMISE_VIOLATION,
                        message="Missing polygon fact in premise",
                        details="Expected Polygon(...) in premise"
                    ))

                polygon_name = polygon_match.group(1)
                if polygon_name != quad_name:
                    return return_error(GeometricError(
                        tier=ErrorTier.TIER2_PREMISE_VIOLATION,
                        message=f"Polygon in premise ({polygon_name}) doesn't match quadrilateral in theorem call ({quad_name})",
                        details="Polygon and quadrilateral argument must match"
                    ))

                # Check if this polygon is defined in our system
                if quad_name not in self.polygons and ''.join(sorted(quad_name)) not in self.polygons:
                    return return_error(GeometricError(
                        tier=ErrorTier.TIER2_PREMISE_VIOLATION,
                        message=f"Polygon {quad_name} is not defined in the system",
                        details="Cannot verify parallelogram properties for undefined polygon"
                    ))

                # Check for the two parallel line statements
                if len(premise_parts) < 3:
                    return return_error(GeometricError(
                        tier=ErrorTier.TIER2_PREMISE_VIOLATION,
                        message="Missing parallel side conditions",
                        details="Need two ParallelBetweenLine statements in premise"
                    ))

                # Parse each parallel statement
                for i, part in enumerate(premise_parts[1:3], 1):
                    parallel_match = re.match(r'ParallelBetweenLine\((\w+),(\w+)\)', part.strip())
                    if not parallel_match:
                        return return_error(GeometricError(
                            tier=ErrorTier.TIER2_PREMISE_VIOLATION,
                            message=f"Invalid parallel line format in premise part {i + 1}",
                            details=f"Expected ParallelBetweenLine(XX,YY) but got {part}"
                        ))

                    # Extract the two lines
                    line1, line2 = parallel_match.groups()

                    # Verify this parallel relationship is already established
                    possible_pairs = [
                        (line1, line2),
                        (line2, line1),
                        (line1[::-1], line2),
                        (line1, line2[::-1]),
                        (line1[::-1], line2[::-1]),
                        (line2[::-1], line1),
                        (line2, line1[::-1]),
                        (line2[::-1], line1[::-1])
                    ]

                    if not any(pair in self.parallel_pairs for pair in possible_pairs):
                        return return_error(GeometricError(
                            tier=ErrorTier.TIER2_PREMISE_VIOLATION,
                            message=f"Parallel relationship between {line1} and {line2} not established",
                            details=f"Known parallel pairs: {self.parallel_pairs}"
                        ))

                # Verify the two lines form opposite sides of the quadrilateral
                # This is a more complex check that would require analyzing the quadrilateral structure
                # For simplicity, we'll skip this check for now

                return True, None
            else:
                return return_error(GeometricError(
                    tier=ErrorTier.TIER1_THEOREM_CALL_SYNTAX_VIOLATION,
                    message="these is no such version for the theorem",
                    details="these is no such version for the theorem parallelogram_judgment_parallel_and_parallel"
                ))





        elif theorem_name == "perpendicular_bisector_property_distance_equal":
            version = args[0]
            if version == "1":
                if len(args) < 3:
                    return return_error(GeometricError(
                        tier=ErrorTier.TIER1_THEOREM_CALL_SYNTAX_VIOLATION,
                        message="Insufficient arguments for perpendicular_bisector_property_distance_equal",
                        details="Expected format: perpendicular_bisector_property_distance_equal(1, bisector, bisected)"
                    ))

                bisector = args[1].strip()  # e.g., "EF"
                bisected = args[2].strip()  # e.g., "AC"

                # Check if the perpendicular bisector relationship is established
                relationship_exists = False

                if hasattr(self, "perpendicular_bisectors"):
                    # Check all variations
                    bisector_variations = [bisector, bisector[::-1]]
                    bisected_variations = [bisected, bisected[::-1]]

                    for b1 in bisector_variations:
                        for b2 in bisected_variations:
                            if (b1, b2) in self.perpendicular_bisectors:
                                relationship_exists = True
                                break
                        if relationship_exists:
                            break

                if not relationship_exists:
                    return return_error(GeometricError(
                        tier=ErrorTier.TIER2_PREMISE_VIOLATION,
                        message=f"Perpendicular bisector relationship not established: {bisector} is not a perpendicular bisector of {bisected}",
                        details="Required for perpendicular_bisector_property_distance_equal theorem"
                    ))

                # All checks passed
                return True, None
            else:
                return return_error(GeometricError(
                    tier=ErrorTier.TIER1_THEOREM_CALL_SYNTAX_VIOLATION,
                    message="these is no such version for the theorem",
                    details="these is no such version for the theorem perpendicular_bisector_property_distance_equal"
                ))



        elif theorem_name == "triangle_area_formula_common":
            version = args[0]
            if version == "1":
                if len(args) < 2:
                    return return_error(GeometricError(
                        tier=ErrorTier.TIER1_THEOREM_CALL_SYNTAX_VIOLATION,
                        message="Missing triangle name for triangle_area_formula_common",
                        details="Expected triangle_area_formula_common(1, triangle)"
                    ))

                triangle = args[1].strip()  # e.g., "DCA"

                # Check if the polygon exists in stored data
                normalized_triangle = self.normalize_triangle(triangle)
                if normalized_triangle not in self.polygons:
                    return return_error(GeometricError(
                        tier=ErrorTier.TIER2_PREMISE_VIOLATION,
                        message=f"Triangle {triangle} not defined in the geometric data",
                        details=f"Known polygons: {self.polygons}"
                    ))

                # Check if a height has been established for this triangle
                if hasattr(self, "triangle_heights") and triangle not in self.triangle_heights:
                    return return_error(GeometricError(
                        tier=ErrorTier.TIER2_PREMISE_VIOLATION,
                        message=f"No height established for triangle {triangle}",
                        details="Height must be established through an altitude theorem first"
                    ))

                return True, None
            else:
                return return_error(GeometricError(
                    tier=ErrorTier.TIER1_THEOREM_CALL_SYNTAX_VIOLATION,
                    message="these is no such version for the theorem",
                    details="these is no such version for the theorem triangle_area_formula_common"
                ))




        elif theorem_name == "altitude_of_triangle_judgment":

            version = args[0]

            if version not in {"1", "2", "3"}:
                return return_error(GeometricError(
                    tier=ErrorTier.TIER1_THEOREM_CALL_SYNTAX_VIOLATION,
                    message="these is no such version for the theorem",
                    details="these is no such version for the theorem altitude_of_triangle_judgment"
                ))

            if len(args) < 3:
                return return_error(GeometricError(

                    tier=ErrorTier.TIER1_THEOREM_CALL_SYNTAX_VIOLATION,

                    message="Insufficient arguments for altitude_of_triangle_judgment",

                    details="Expected format: altitude_of_triangle_judgment(version, altitude_line, triangle)"

                ))

            altitude_line = args[1].strip()  # e.g., "AD"

            triangle = args[2].strip()  # e.g., "ABC"

            # Parse the premise parts

            premise_parts = premise.split('&')

            # Check for polygon fact

            polygon_match = re.search(r'Polygon\(' + re.escape(triangle) + r'\)', premise)

            if not polygon_match:
                return return_error(GeometricError(

                    tier=ErrorTier.TIER2_PREMISE_VIOLATION,

                    message=f"Missing Polygon({triangle}) fact in premise",

                    details="altitude_of_triangle_judgment requires the triangle to be defined"

                ))

            # Verify the triangle exists in our system

            normalized_triangle = self.normalize_triangle(triangle)

            if normalized_triangle not in self.polygons:
                return return_error(GeometricError(

                    tier=ErrorTier.TIER2_PREMISE_VIOLATION,

                    message=f"Triangle {triangle} is not defined in the system",

                    details=f"Known polygons: {self.polygons}"

                ))

            # Check for line fact

            line_match = re.search(r'Line\(' + re.escape(altitude_line) + r'\)', premise)

            if not line_match:
                return return_error(GeometricError(

                    tier=ErrorTier.TIER2_PREMISE_VIOLATION,

                    message=f"Missing Line({altitude_line}) fact in premise",

                    details="altitude_of_triangle_judgment requires the altitude line to be defined"

                ))

            # Determine expected collinearity and right angle based on version

            expected_collinear = None

            expected_angle = None

            # Extract opposite side vertices (those not connected to altitude's vertex)

            altitude_vertex = altitude_line[0]  # e.g., "A"

            opposite_vertices = [v for v in triangle if v != altitude_vertex]  # e.g., ["B", "C"]

            altitude_foot = altitude_line[1]  # e.g., "D"

            if version == "1":

                # Version 1: Collinear(BDC) & Equal(MeasureOfAngle(BDA),90)

                expected_collinear = f"{opposite_vertices[0]}{altitude_foot}{opposite_vertices[1]}"  # "BDC"

                expected_angle = f"{opposite_vertices[0]}{altitude_foot}{altitude_vertex}"  # "BDA"

            elif version == "2":

                # Version 2: Collinear(DBC) & Equal(MeasureOfAngle(ADB),90)

                expected_collinear = f"{altitude_foot}{opposite_vertices[0]}{opposite_vertices[1]}"  # "DBC"

                expected_angle = f"{altitude_vertex}{altitude_foot}{opposite_vertices[0]}"  # "ADB"

            elif version == "3":

                # Version 3: Collinear(BCD) & Equal(MeasureOfAngle(CDA),90)

                expected_collinear = f"{opposite_vertices[0]}{opposite_vertices[1]}{altitude_foot}"  # "BCD"

                expected_angle = f"{opposite_vertices[1]}{altitude_foot}{altitude_vertex}"  # "CDA"

            # Check for collinearity fact

            collinear_match = re.search(r'Collinear\((\w+)\)', premise)

            if not collinear_match:
                return return_error(GeometricError(

                    tier=ErrorTier.TIER2_PREMISE_VIOLATION,

                    message="Missing collinearity fact in premise",

                    details=f"Version {version} requires Collinear({expected_collinear})"

                ))

            collinear_points = collinear_match.group(1)

            # Normalize for comparison to handle different orderings

            normalized_expected = ''.join(sorted(expected_collinear))

            normalized_actual = ''.join(sorted(collinear_points))

            if normalized_expected != normalized_actual:
                return return_error(GeometricError(

                    tier=ErrorTier.TIER2_PREMISE_VIOLATION,

                    message=f"Collinearity mismatch: expected Collinear({expected_collinear}), got Collinear({collinear_points})",

                    details=f"Version {version} requires specific collinearity"

                ))

            # Check if this collinearity exists in our system

            collinear_found = False

            for fact in self.collinear_facts:

                fact_str = ''.join(fact)

                normalized_fact = ''.join(sorted(fact_str))

                if normalized_fact == normalized_actual:
                    collinear_found = True

                    break

            if not collinear_found:
                return return_error(GeometricError(

                    tier=ErrorTier.TIER2_PREMISE_VIOLATION,

                    message=f"Collinearity fact Collinear({collinear_points}) not established",

                    details=f"Known collinear facts: {[''.join(fact) for fact in self.collinear_facts]}"

                ))

            # Check for right angle fact

            angle_match = re.search(r'Equal\(MeasureOfAngle\((\w{3})\),90\)', premise)

            if not angle_match:
                return return_error(GeometricError(

                    tier=ErrorTier.TIER2_PREMISE_VIOLATION,

                    message="Missing right angle fact in premise",

                    details=f"Version {version} requires Equal(MeasureOfAngle({expected_angle}),90)"

                ))

            angle_name = angle_match.group(1)

            # Since angles can be represented in different orders, normalize by ensuring

            # the middle point is the same and the endpoints are the same (order doesn't matter)

            if angle_name[1] != expected_angle[1] or sorted([angle_name[0], angle_name[2]]) != sorted(
                    [expected_angle[0], expected_angle[2]]):
                return return_error(GeometricError(

                    tier=ErrorTier.TIER2_PREMISE_VIOLATION,

                    message=f"Angle mismatch: expected MeasureOfAngle({expected_angle}), got MeasureOfAngle({angle_name})",

                    details=f"Version {version} requires a specific right angle"

                ))

            # Verify the angle is actually 90 degrees in the solver

            angle_var = self.add_angle(angle_name[0], angle_name[1], angle_name[2])

            if self.solver.check() == sat:

                temp_solver = Solver()

                for c in self.solver.assertions():
                    temp_solver.add(c)

                temp_solver.add(angle_var != 90)

                if temp_solver.check() != unsat:
                    return return_error(GeometricError(

                        tier=ErrorTier.TIER2_PREMISE_VIOLATION,

                        message=f"Angle {angle_name} is not constrained to be 90°",

                        details="The right angle constraint must be enforced by the solver"

                    ))

            # All checks passed

            return True, None

        elif theorem_name == "flat_angle":
            # Expected arguments: version, angle
            version = args[0]
            if version == "1":
                if len(args) < 2:
                    return return_error(GeometricError(
                        tier=ErrorTier.TIER1_THEOREM_CALL_SYNTAX_VIOLATION,
                        message="Insufficient arguments for flat_angle",
                        details="Expected format: flat_angle(1, angle)"
                    ))

                angle_name = args[1].strip()  # e.g., "BPA"

                # Check that the three points are collinear
                collinear_found = False

                # Normalize the angle points to match how collinearity is stored
                points = list(angle_name)  # Convert "BPA" to ['B', 'P', 'A']

                for fact in self.collinear_facts:
                    # Convert fact list to string for comparison
                    fact_str = ''.join(fact)

                    # Check if all points from the angle are in this collinear fact
                    if all(p in fact_str for p in points):
                        collinear_found = True
                        break

                if not collinear_found:
                    return return_error(GeometricError(
                        tier=ErrorTier.TIER2_PREMISE_VIOLATION,
                        message=f"Points {angle_name} are not proven collinear",
                        details="Required collinearity for flat_angle theorem is not established"
                    ))

                # All checks passed
                return True, None
            else:
                return return_error(GeometricError(
                    tier=ErrorTier.TIER1_THEOREM_CALL_SYNTAX_VIOLATION,
                    message="these is no such version for the theorem",
                    details="these is no such version for the theorem flat_angle"
                ))





        elif theorem_name == "circle_property_circular_power_chord_and_chord":

            version = args[0]

            if version == "1":

                if len(args) < 4:
                    return return_error(GeometricError(

                        tier=ErrorTier.TIER1_THEOREM_CALL_SYNTAX_VIOLATION,

                        message="Insufficient arguments for circle_property_circular_power_chord_and_chord",

                        details="Expected format: circle_property_circular_power_chord_and_chord(1, chord1, chord2, circle)"

                    ))

                chord1 = args[1].strip()  # e.g., "BEA"

                chord2 = args[2].strip()  # e.g., "DEC"

                circle_token = args[3].strip()  # e.g., "F"

                # Count how many points from each chord are on the circle

                chord1_points_on_circle = []

                chord2_points_on_circle = []

                for point in chord1:

                    for fact in self.cocircular_facts:

                        if fact[0] == circle_token and point in fact[1:]:
                            chord1_points_on_circle.append(point)

                            break

                for point in chord2:

                    for fact in self.cocircular_facts:

                        if fact[0] == circle_token and point in fact[1:]:
                            chord2_points_on_circle.append(point)

                            break

                # We need at least 2 points from each chord to be on the circle

                if len(chord1_points_on_circle) < 2:
                    return return_error(GeometricError(

                        tier=ErrorTier.TIER2_PREMISE_VIOLATION,

                        message=f"Not enough points from chord {chord1} are on circle {circle_token}",

                        details=f"Found only points {chord1_points_on_circle} on circle {circle_token}, need at least 2"

                    ))

                if len(chord2_points_on_circle) < 2:
                    return return_error(GeometricError(

                        tier=ErrorTier.TIER2_PREMISE_VIOLATION,

                        message=f"Not enough points from chord {chord2} are on circle {circle_token}",

                        details=f"Found only points {chord2_points_on_circle} on circle {circle_token}, need at least 2"

                    ))

                # Check for collinearity facts in the stored collinear_facts

                collinear1_found = False

                collinear2_found = False

                # Normalize the chord strings to match how collinearity is stored

                norm_chord1 = self.normalize_collinear_points(chord1)

                norm_chord2 = self.normalize_collinear_points(chord2)

                for fact in self.collinear_facts:

                    # Convert fact list to string for comparison

                    fact_str = ''.join(fact)

                    # Normalize for comparison

                    norm_fact = self.normalize_collinear_points(fact_str)

                    # Check if all points from the chord are in this fact

                    if all(p in norm_fact for p in norm_chord1):
                        collinear1_found = True

                    if all(p in norm_fact for p in norm_chord2):
                        collinear2_found = True

                if not collinear1_found:
                    return return_error(GeometricError(

                        tier=ErrorTier.TIER2_PREMISE_VIOLATION,

                        message=f"Missing collinearity fact for points in {chord1}",

                        details=f"Points {chord1} must be collinear"

                    ))

                if not collinear2_found:
                    return return_error(GeometricError(

                        tier=ErrorTier.TIER2_PREMISE_VIOLATION,

                        message=f"Missing collinearity fact for points in {chord2}",

                        details=f"Points {chord2} must be collinear"

                    ))

                # All checks passed

                return True, None

            else:

                return return_error(GeometricError(
                    tier=ErrorTier.TIER1_THEOREM_CALL_SYNTAX_VIOLATION,
                    message="these is no such version for the theorem",
                    details="these is no such version for the theorem circle_property_circular_power_chord_and_chord"
                ))



        elif theorem_name == "round_angle":
            # Expected arguments: version, angle1, angle2
            version = args[0]
            if version != "-99":
                return return_error(GeometricError(
                    tier=ErrorTier.TIER1_THEOREM_CALL_SYNTAX_VIOLATION,
                    message="this theorem is not supported by this solver please give a profe without it",
                    details="the round_angle is not supported by this solver please give a profe without it"
                ))

            if version == "1":
                if len(args) < 3:
                    return return_error(GeometricError(
                        tier=ErrorTier.TIER1_THEOREM_CALL_SYNTAX_VIOLATION,
                        message="Insufficient arguments for round_angle",
                        details="Expected format: round_angle(1, angle1, angle2)"
                    ))

                angle1 = args[1].strip()  # e.g., "FBC"
                angle2 = args[2].strip()  # e.g., "CBF"

                # Check if both angles exist in our system
                normalized_angle1 = self.normalize_angle_name(angle1)
                normalized_angle2 = self.normalize_angle_name(angle2)

                angle1_var_name = f"angle_{normalized_angle1}"
                angle2_var_name = f"angle_{normalized_angle2}"

                if angle1_var_name not in self.angles:
                    return return_error(GeometricError(
                        tier=ErrorTier.TIER2_PREMISE_VIOLATION,
                        message=f"Angle {angle1} is not defined",
                        details="Required angle for round_angle theorem is not established"
                    ))

                if angle2_var_name not in self.angles:
                    return return_error(GeometricError(
                        tier=ErrorTier.TIER2_PREMISE_VIOLATION,
                        message=f"Angle {angle2} is not defined",
                        details="Required angle for round_angle theorem is not established"
                    ))

                # All checks passed
                return True, None
            else:
                return return_error(GeometricError(
                    tier=ErrorTier.TIER1_THEOREM_CALL_SYNTAX_VIOLATION,
                    message=f"Unsupported version {version} for round_angle"
                ))




        elif theorem_name == "cosine_theorem":
            version = args[0]
            if version == "1":
                if len(args) < 2:
                    return return_error(GeometricError(
                        tier=ErrorTier.TIER1_THEOREM_CALL_SYNTAX_VIOLATION,
                        message="Missing triangle argument for cosine_theorem",
                        details="Expected cosine_theorem(1, triangle)"
                    ))

                triangle = args[1].strip()
                normalized_triangle = self.normalize_triangle(triangle)

                # Check if the triangle exists in the polygons stored in the class attributes
                if normalized_triangle not in self.polygons:
                    return return_error(GeometricError(
                        tier=ErrorTier.TIER2_PREMISE_VIOLATION,
                        message=f"Triangle {triangle} not defined in the geometric data",
                        details=f"Known polygons: {self.polygons}"
                    ))

                return True, None
            else:
                return return_error(GeometricError(
                    tier=ErrorTier.TIER1_THEOREM_CALL_SYNTAX_VIOLATION,
                    message="these is no such version for the theorem",
                    details="these is no such version for the theorem cosine_theorem"
                ))


        elif theorem_name == "line_addition":
            version = args[0]
            if version == "1":
                if len(args) < 3:
                    return return_error(GeometricError(
                        tier=ErrorTier.TIER1_THEOREM_CALL_SYNTAX_VIOLATION,
                        message="Missing arguments for line_addition",
                        details="Expected: line_addition(1, line1, line2)"
                    ))

                line1 = args[1].strip()  # e.g. "CD"
                line2 = args[2].strip()  # e.g. "DA"

                # Extract points from premise collinearity
                collinear_match = re.search(r'Collinear\((\w+)\)', premise)
                if not collinear_match:
                    return return_error(GeometricError(
                        tier=ErrorTier.TIER2_PREMISE_VIOLATION,
                        message="Missing collinearity fact in premise",
                        details="line_addition requires collinear points"
                    ))

                collinear_points = collinear_match.group(1)  # e.g. "CDA"
                normalized_collinear = self.normalize_collinear_points(collinear_points)

                # Check if collinearity fact exists
                if not any(self.normalize_collinear_points(''.join(fact)) == normalized_collinear
                           for fact in self.collinear_facts):
                    return return_error(GeometricError(
                        tier=ErrorTier.TIER2_PREMISE_VIOLATION,
                        message=f"Points {collinear_points} not proven collinear",
                        details=f"Known collinear facts: {self.collinear_facts}"
                    ))

                # Verify that the lines share points in the collinear sequence
                if not (all(p in collinear_points for p in line1) and
                        all(p in collinear_points for p in line2)):
                    return return_error(GeometricError(
                        tier=ErrorTier.TIER2_PREMISE_VIOLATION,
                        message="Lines must be part of the collinear sequence",
                        details=f"Lines {line1} and {line2} must be formed by points in {collinear_points}"
                    ))

                # Check if lines share an endpoint
                common_point = set(line1).intersection(set(line2))
                if not common_point:
                    return return_error(GeometricError(
                        tier=ErrorTier.TIER2_PREMISE_VIOLATION,
                        message="Lines must share an endpoint",
                        details=f"Lines {line1} and {line2} must have a common point"
                    ))

                return True, None
            else:
                return return_error(GeometricError(
                        tier=ErrorTier.TIER1_THEOREM_CALL_SYNTAX_VIOLATION,
                        message="these is no such version for the theorem",
                        details="these is no such version for the theorem line_addition"
                    ))




        elif theorem_name == "perpendicular_bisector_judgment_distance_equal":
            version = args[0]
            if version == "1":
                if len(args) < 3:
                    return return_error(GeometricError(
                        tier=ErrorTier.TIER1_THEOREM_CALL_SYNTAX_VIOLATION,
                        message="Missing arguments for perpendicular_bisector_judgment_distance_equal",
                        details="Expected: perpendicular_bisector_judgment_distance_equal(1, bisector_line, bisected_line)"
                    ))

                bisector = args[1].strip()  # e.g. "BD"
                bisected = args[2].strip()  # e.g. "CA"

                # Parse the premise parts
                premise_parts = premise.split('&')

                # Check collinearity fact
                collinear_part = next((p for p in premise_parts if p.startswith('Collinear(')), None)
                if not collinear_part:
                    return return_error(GeometricError(
                        tier=ErrorTier.TIER2_PREMISE_VIOLATION,
                        message="Missing collinearity fact in premise",
                        details="Required for perpendicular bisector"
                    ))

                # Extract collinear points and check
                collinear_match = re.search(r'Collinear\((\w+)\)', collinear_part)
                if collinear_match:
                    collinear_points = collinear_match.group(1)
                    normalized_collinear = self.normalize_collinear_points(collinear_points)
                    if not any(self.normalize_collinear_points(''.join(fact)) == normalized_collinear
                               for fact in self.collinear_facts):
                        return return_error(GeometricError(
                            tier=ErrorTier.TIER2_PREMISE_VIOLATION,
                            message=f"Points {collinear_points} not proven collinear",
                            details=f"Known collinear facts: {self.collinear_facts}"
                        ))

                # Check angle = 90° fact
                angle_eq_part = next((p for p in premise_parts if p.startswith('Equal(MeasureOfAngle(')), None)
                if not angle_eq_part:
                    return return_error(GeometricError(
                        tier=ErrorTier.TIER2_PREMISE_VIOLATION,
                        message="Missing right angle fact in premise",
                        details="Perpendicular bisector requires 90° angle"
                    ))

                # Check angle equality matches required right angle
                angle_match = re.search(r'Equal\(MeasureOfAngle\((\w{3})\),90\)', angle_eq_part)
                if not angle_match:
                    return return_error(GeometricError(
                        tier=ErrorTier.TIER2_PREMISE_VIOLATION,
                        message="Angle value must be 90 degrees",
                        details="Required for perpendicular bisector"
                    ))

                # Check length equality fact
                length_eq_part = next((p for p in premise_parts if 'LengthOfLine' in p), None)
                if not length_eq_part:
                    return return_error(GeometricError(
                        tier=ErrorTier.TIER2_PREMISE_VIOLATION,
                        message="Missing length equality in premise",
                        details="Required for perpendicular bisector"
                    ))

                # All premise checks passed, return success
                return True, None
            else:
                return return_error(GeometricError(
                    tier=ErrorTier.TIER1_THEOREM_CALL_SYNTAX_VIOLATION,
                    message="these is no such version for the theorem",
                    details="these is no such version for the theorem perpendicular_bisector_judgment_distance_equal"
                ))



        elif theorem_name == "altitude_of_quadrilateral_judgment_diagonal":

            version = args[0].strip()

            if version not in {"1", "2"}:
                return return_error(GeometricError(
                    tier=ErrorTier.TIER1_THEOREM_CALL_SYNTAX_VIOLATION,
                    message="these is no such version for the theorem",
                    details="these is no such version for the theorem altitude_of_quadrilateral_judgment_diagonal"
                ))


            if len(args) < 2:
                return return_error(GeometricError(

                    tier=ErrorTier.TIER1_THEOREM_CALL_SYNTAX_VIOLATION,

                    message="Missing arguments for altitude_of_quadrilateral_judgment_diagonal",

                    details="Expected: altitude_of_quadrilateral_judgment_diagonal(version, quadrilateral)"

                ))

            quad = args[1].strip()  # e.g., "ABCD"

            # Check shape type in premise

            shape_match = re.search(r'\(Parallelogram\(' + re.escape(quad) +

                                    r'\)\|Trapezoid\(' + re.escape(quad) + r'\)\)', premise)

            if not shape_match:
                return return_error(GeometricError(

                    tier=ErrorTier.TIER2_PREMISE_VIOLATION,

                    message=f"Missing shape definition for {quad} in premise",

                    details="Required: (Parallelogram(ABCD)|Trapezoid(ABCD))"

                ))

            # Verify the quadrilateral is a parallelogram or trapezoid

            is_valid_shape = False

            if quad in self.parallelograms:

                is_valid_shape = True

            elif hasattr(self, 'trapezoids') and quad in self.trapezoids:

                is_valid_shape = True

            if not is_valid_shape:
                return return_error(GeometricError(

                    tier=ErrorTier.TIER2_PREMISE_VIOLATION,

                    message=f"Quadrilateral {quad} is not defined as a parallelogram or trapezoid",

                    details="Required for altitude_of_quadrilateral_judgment_diagonal"

                ))

            # Determine expected diagonal and angle based on version

            expected_diagonal = None

            expected_angle = None

            if version == "1":

                # Version 1: Line(AC) & Equal(MeasureOfAngle(BCA),90)

                expected_diagonal = f"{quad[0]}{quad[2]}"  # AC

                expected_angle = f"{quad[1]}{quad[2]}{quad[0]}"  # BCA

            elif version == "2":

                # Version 2: Line(DB) & Equal(MeasureOfAngle(DBC),90)

                expected_diagonal = f"{quad[3]}{quad[1]}"  # DB

                expected_angle = f"{quad[3]}{quad[1]}{quad[2]}"  # DBC

            # Check for Line fact

            line_match = re.search(r'Line\((\w+)\)', premise)

            if not line_match:
                return return_error(GeometricError(

                    tier=ErrorTier.TIER2_PREMISE_VIOLATION,

                    message="Missing Line fact in premise",

                    details=f"Version {version} requires Line({expected_diagonal})"

                ))

            diagonal = line_match.group(1)

            if diagonal != expected_diagonal and diagonal != expected_diagonal[::-1]:
                return return_error(GeometricError(

                    tier=ErrorTier.TIER2_PREMISE_VIOLATION,

                    message=f"Line mismatch: expected Line({expected_diagonal}), got Line({diagonal})",

                    details=f"Version {version} requires a specific diagonal"

                ))

            # Check for right angle

            angle_match = re.search(r'Equal\(MeasureOfAngle\((\w{3})\),90\)', premise)

            if not angle_match:
                return return_error(GeometricError(

                    tier=ErrorTier.TIER2_PREMISE_VIOLATION,

                    message="Missing right angle fact in premise",

                    details=f"Version {version} requires Equal(MeasureOfAngle({expected_angle}),90)"

                ))

            angle_name = angle_match.group(1)

            # Normalize angle for comparison

            if sorted(angle_name) != sorted(expected_angle) or angle_name[1] != expected_angle[1]:
                return return_error(GeometricError(

                    tier=ErrorTier.TIER2_PREMISE_VIOLATION,

                    message=f"Angle mismatch: expected MeasureOfAngle({expected_angle}), got MeasureOfAngle({angle_name})",

                    details=f"Version {version} requires a specific right angle"

                ))

            # Verify the angle is actually 90 degrees in the solver

            angle_var = self.add_angle(angle_name[0], angle_name[1], angle_name[2])

            if self.solver.check() == sat:

                temp_solver = Solver()

                for c in self.solver.assertions():
                    temp_solver.add(c)

                temp_solver.add(angle_var != 90)

                if temp_solver.check() != unsat:
                    return return_error(GeometricError(

                        tier=ErrorTier.TIER2_PREMISE_VIOLATION,

                        message=f"Angle {angle_name} is not constrained to be 90°",

                        details="The right angle constraint must be enforced by the solver"

                    ))

            return True, None





        elif theorem_name == "altitude_of_quadrilateral_judgment_left_vertex":

            version = args[0].strip()

            if version not in {"1", "2", "3"}:
                return return_error(GeometricError(
                    tier=ErrorTier.TIER1_THEOREM_CALL_SYNTAX_VIOLATION,
                    message="these is no such version for the theorem",
                    details="these is no such version for the theorem altitude_of_quadrilateral_judgment_left_vertex"
                ))

            if len(args) < 3:
                return return_error(GeometricError(

                    tier=ErrorTier.TIER1_THEOREM_CALL_SYNTAX_VIOLATION,

                    message="Missing arguments for altitude_of_quadrilateral_judgment_left_vertex",

                    details="Expected: altitude_of_quadrilateral_judgment_left_vertex(version, altitude_line, quadrilateral)"

                ))

            altitude_line = args[1].strip()  # e.g., "AF"

            quad_name = args[2].strip()  # e.g., "ABCD"

            # Check the quadrilateral is a parallelogram or trapezoid

            if not (quad_name in self.parallelograms or

                    (hasattr(self, 'trapezoids') and quad_name in self.trapezoids)):
                return return_error(GeometricError(

                    tier=ErrorTier.TIER2_PREMISE_VIOLATION,

                    message=f"Quadrilateral {quad_name} is not defined as a parallelogram or trapezoid",

                    details="Required for altitude_of_quadrilateral_judgment_left_vertex"

                ))

            # Check for shape type in premise

            shape_match = re.search(r'\(Parallelogram\(' + re.escape(quad_name) +

                                    r'\)\|Trapezoid\(' + re.escape(quad_name) + r'\)\)', premise)

            if not shape_match:
                return return_error(GeometricError(

                    tier=ErrorTier.TIER2_PREMISE_VIOLATION,

                    message=f"Missing shape definition for {quad_name} in premise",

                    details="Required: (Parallelogram(ABCD)|Trapezoid(ABCD))"

                ))

            # Check for Line fact

            line_match = re.search(r'Line\(' + re.escape(altitude_line) + r'\)', premise)

            if not line_match:
                return return_error(GeometricError(

                    tier=ErrorTier.TIER2_PREMISE_VIOLATION,

                    message=f"Missing Line({altitude_line}) fact in premise",

                    details="Required for altitude definition"

                ))

            # Version-specific checks for collinearity

            expected_collinear = None

            if version == "1":

                # Version 1: Collinear(BFC)

                point_B = quad_name[1]  # Second vertex

                point_C = quad_name[2]  # Third vertex

                point_F = altitude_line[1]  # Second point of altitude

                expected_collinear = f"{point_B}{point_F}{point_C}"

            elif version == "2":

                # Version 2: Collinear(FBC)

                point_F = altitude_line[1]  # Second point of altitude

                point_B = quad_name[1]  # Second vertex

                point_C = quad_name[2]  # Third vertex

                expected_collinear = f"{point_F}{point_B}{point_C}"

            elif version == "3":

                # Version 3: Collinear(BCF)

                point_B = quad_name[1]  # Second vertex

                point_C = quad_name[2]  # Third vertex

                point_F = altitude_line[1]  # Second point of altitude

                expected_collinear = f"{point_B}{point_C}{point_F}"

            # Check for collinearity fact

            collinear_match = re.search(r'Collinear\((\w+)\)', premise)

            if not collinear_match:
                return return_error(GeometricError(

                    tier=ErrorTier.TIER2_PREMISE_VIOLATION,

                    message="Missing Collinear fact in premise",

                    details=f"Version {version} requires Collinear({expected_collinear})"

                ))

            # Get the actual collinear points from premise

            collinear_points = collinear_match.group(1)

            # Check that the expected points are in the collinearity fact

            # We use a normalized version to handle different orderings

            normalized_expected = ''.join(sorted(expected_collinear))

            normalized_actual = ''.join(sorted(collinear_points))

            if normalized_expected != normalized_actual:
                return return_error(GeometricError(

                    tier=ErrorTier.TIER2_PREMISE_VIOLATION,

                    message=f"Collinearity mismatch: expected Collinear({expected_collinear}), got Collinear({collinear_points})",

                    details=f"Version {version} requires specific collinearity"

                ))

            # Version-specific checks for right angle

            expected_angle = None

            if version == "1":

                # Version 1: Equal(MeasureOfAngle(BFA),90)

                point_B = quad_name[1]  # Second vertex

                point_F = altitude_line[1]  # Second point of altitude

                point_A = altitude_line[0]  # First point of altitude

                expected_angle = f"{point_B}{point_F}{point_A}"

            elif version == "2":

                # Version 2: Equal(MeasureOfAngle(AFB),90)

                point_A = altitude_line[0]  # First point of altitude

                point_F = altitude_line[1]  # Second point of altitude

                point_B = quad_name[1]  # Second vertex

                expected_angle = f"{point_A}{point_F}{point_B}"

            elif version == "3":

                # Version 3: Equal(MeasureOfAngle(CFA),90)

                point_C = quad_name[2]  # Third vertex

                point_F = altitude_line[1]  # Second point of altitude

                point_A = altitude_line[0]  # First point of altitude

                expected_angle = f"{point_C}{point_F}{point_A}"

            # Check for right angle fact

            angle_match = re.search(r'Equal\(MeasureOfAngle\((\w{3})\),90\)', premise)

            if not angle_match:
                return return_error(GeometricError(

                    tier=ErrorTier.TIER2_PREMISE_VIOLATION,

                    message="Missing right angle fact in premise",

                    details=f"Version {version} requires Equal(MeasureOfAngle({expected_angle}),90)"

                ))

            # Get the actual angle from premise

            angle_name = angle_match.group(1)

            # Check that it's the expected angle

            # Since angles can be specified in different orders, normalize by ensuring the middle point is the same

            if angle_name[1] != expected_angle[1] or sorted([angle_name[0], angle_name[2]]) != sorted(
                    [expected_angle[0], expected_angle[2]]):
                return return_error(GeometricError(

                    tier=ErrorTier.TIER2_PREMISE_VIOLATION,

                    message=f"Angle mismatch: expected MeasureOfAngle({expected_angle}), got MeasureOfAngle({angle_name})",

                    details=f"Version {version} requires a specific right angle"

                ))

            return True, None







        elif theorem_name == "parallelogram_property_opposite_line_equal":
            version = args[0]

            if version != "1":  # Updated to include version "2"
                return return_error(GeometricError(
                    tier=ErrorTier.TIER1_THEOREM_CALL_SYNTAX_VIOLATION,
                    message="these is no such version for the theorem",
                    details="these is no such version for the theorem parallelogram_property_opposite_line_equal"
                ))

            if len(args) < 2:
                return (False, GeometricError(
                    tier=ErrorTier.TIER1_THEOREM_CALL_SYNTAX_VIOLATION,
                    message="Missing parallelogram name for parallelogram_property_opposite_line_equal."
                ))
            para = args[1].strip()
            if para not in self.parallelograms:
                return (False, GeometricError(
                    tier=ErrorTier.TIER2_PREMISE_VIOLATION,
                    message=f"Parallelogram {para} is not defined."
                ))
            return (True, None)

        elif theorem_name == "parallelogram_area_formula_common":
            version = args[0]

            if version != "1":  # Updated to include version "2"
                return return_error(GeometricError(
                    tier=ErrorTier.TIER1_THEOREM_CALL_SYNTAX_VIOLATION,
                    message="these is no such version for the theorem",
                    details="these is no such version for the theorem parallelogram_area_formula_common"
                ))

            if len(args) < 2:
                return (False, GeometricError(
                    tier=ErrorTier.TIER1_THEOREM_CALL_SYNTAX_VIOLATION,
                    message="Missing quadrilateral name for parallelogram_area_formula_common."
                ))
            quad = args[1].strip()
            if quad not in self.parallelograms:
                return (False, GeometricError(
                    tier=ErrorTier.TIER2_PREMISE_VIOLATION,
                    message=f"Quadrilateral {quad} is not defined as a parallelogram."
                ))
            return (True, None)


        elif theorem_name == "isosceles_triangle_property_angle_equal":
            version = args[0]

            if version != "1":
                return return_error(GeometricError(
                    tier=ErrorTier.TIER1_THEOREM_CALL_SYNTAX_VIOLATION,
                    message="these is no such version for the theorem",
                    details="these is no such version for the theorem isosceles_triangle_property_angle_equal"
                ))
            # Expected theorem call: isosceles_triangle_property_angle_equal(1, T)

            # where T is a triangle name (e.g., "JPN").

            if len(args) < 2:
                return return_error(GeometricError(

                    tier=ErrorTier.TIER1_THEOREM_CALL_SYNTAX_VIOLATION,

                    message="Missing triangle name for isosceles_triangle_property_angle_equal."

                ))

            tri = args[1].strip()  # e.g., "JPN"

            # Generate all cyclic variations of the triangle T.

            def cyclic_variations(s):

                return {s[i:] + s[:i] for i in range(len(s))}

            variations = cyclic_variations(tri)

            # Check that at least one cyclic variation of T is recorded as isosceles.

            if not (variations & getattr(self, 'isosceles_triangles', set())):
                return return_error(GeometricError(

                    tier=ErrorTier.TIER2_PREMISE_VIOLATION,

                    message=f"Triangle {tri} is not recorded as isosceles.",

                    details="Ensure that isosceles_triangle_judgment_line_equal has been applied."

                ))

            return True, None

        elif theorem_name == "isosceles_triangle_judgment_line_equal":

            # Expected theorem call: isosceles_triangle_judgment_line_equal(1, T)

            # where T is a triangle name (for example, "JPN").
            version = args[0]

            if version != "1":  # Updated to include version "2"
                return return_error(GeometricError(
                    tier=ErrorTier.TIER1_THEOREM_CALL_SYNTAX_VIOLATION,
                    message="these is no such version for the theorem",
                    details="these is no such version for the theorem isosceles_triangle_judgment_line_equal"
                ))

            if len(args) < 2:
                return return_error(GeometricError(

                    tier=ErrorTier.TIER1_THEOREM_CALL_SYNTAX_VIOLATION,

                    message="Missing triangle name for isosceles_triangle_judgment_line_equal."

                ))

            tri = args[1].strip()  # e.g., "JPN"

            # Check that the triangle is defined (i.e. a polygon fact exists)

            if self.normalize_triangle(tri) not in self.polygons:
                return return_error(GeometricError(

                    tier=ErrorTier.TIER2_PREMISE_VIOLATION,

                    message=f"Polygon for triangle {tri} is missing",

                    details="The construction data did not define this polygon."

                ))

            # We now want to check that the premise contains an equality between two sides

            # sharing a common vertex for some cyclic rotation of tri.

            # For a triangle ABC, one possibility is Equal(LengthOfLine(AB),LengthOfLine(AC)).

            def cyclic_rotations(s):

                rotations = []

                for i in range(len(s)):
                    rotations.append(s[i:] + s[:i])

                return rotations

            rotations = cyclic_rotations(tri)

            found_equality = False

            for r in rotations:

                if self.check_length_equality(r[0:2], r[0] + r[2]):
                    found_equality = True

                    break

            if not found_equality:
                return return_error(GeometricError(

                    tier=ErrorTier.TIER2_PREMISE_VIOLATION,

                    message="Expected equality between two sides sharing a vertex not found in the premise.",

                    details=f"Premise: {premise}"

                ))

            return True, None


        elif theorem_name == "rectangle_property_diagonal_equal":
            version = args[0]

            if version != "1":  # Updated to include version "2"
                return return_error(GeometricError(
                    tier=ErrorTier.TIER1_THEOREM_CALL_SYNTAX_VIOLATION,
                    message="these is no such version for the theorem",
                    details="these is no such version for the theorem rectangle_property_diagonal_equal"
                ))
            # Expected theorem call: rectangle_property_diagonal_equal(1, PNML)

            # And the premise should include a clause like "Rectangle(PNML)".

            if len(args) < 2:
                return return_error(GeometricError(

                    tier=ErrorTier.TIER1_THEOREM_CALL_SYNTAX_VIOLATION,

                    message="Missing rectangle name for rectangle_property_diagonal_equal."

                ))

            rect_name = args[1].strip()  # e.g., "PNML"

            # Check that a rectangle equivalent to rect_name (via cyclic variations) was declared.

            if not (rect_name in self.rectangles):
                return return_error(GeometricError(

                    tier=ErrorTier.TIER2_PREMISE_VIOLATION,

                    message=f"Rectangle {rect_name} is not defined.",

                    details=f"Defined rectangles (cyclic variations): {self.rectangles}"

                ))

            # Since the rectangle fact is present, we assume that the diagonal lines will be

            # handled in later steps. Do not check for the existence of the diagonal lines here.

            return True, None


        elif theorem_name == "parallelogram_property_diagonal_bisection":
            # Expected theorem call: parallelogram_property_diagonal_bisection(1, PNML, J)
            # The premise should include a parallelogram fact for PNML and
            # collinear facts showing that the intersection point J lies on both diagonals.
            version = args[0]

            if version != "1":  # Updated to include version "2"
                return return_error(GeometricError(
                    tier=ErrorTier.TIER1_THEOREM_CALL_SYNTAX_VIOLATION,
                    message="these is no such version for the theorem",
                    details="these is no such version for the theorem parallelogram_property_diagonal_bisection"
                ))

            if len(args) < 3:
                return return_error(GeometricError(
                    tier=ErrorTier.TIER1_THEOREM_CALL_SYNTAX_VIOLATION,
                    message="Insufficient arguments for parallelogram_property_diagonal_bisection."
                ))
            para_name = args[1].strip()  # e.g., "PNML"
            mid_candidate = args[2].strip()  # e.g., "J"

            # --- Check that a parallelogram fact is recorded for the given parallelogram.
            # (Assume that when parsing TEXT_CDL, all cyclic variations of any parallelogram are added to self.parallelograms.)
            if not (get_cyclic_variations(para_name) & self.parallelograms):
                return return_error(GeometricError(
                    tier=ErrorTier.TIER2_PREMISE_VIOLATION,
                    message=f"Parallelogram {para_name} is not defined.",
                    details=f"Defined parallelograms: {self.parallelograms}"
                ))

            # --- Compute the expected collinear facts.
            # For a quadrilateral (parallelogram) with vertices in order, the diagonals are:
            #    diag1: from the 1st vertex to the 3rd, and diag2: from the 2nd vertex to the 4th.
            if len(para_name) < 4:
                return return_error(GeometricError(
                    tier=ErrorTier.TIER1_THEOREM_CALL_SYNTAX_VIOLATION,
                    message=f"Parallelogram name {para_name} is invalid (expected 4 letters)."
                ))
            diag1_expected = para_name[0] + mid_candidate + para_name[2]  # e.g., "PJM"
            diag2_expected = para_name[1] + mid_candidate + para_name[3]  # e.g., "NJL"

            norm_diag1 = self.normalize_collinear_points(diag1_expected)
            norm_diag2 = self.normalize_collinear_points(diag2_expected)

            found_diag1 = any(self.normalize_collinear_points("".join(fact)) == norm_diag1
                              for fact in self.collinear_facts)
            found_diag2 = any(self.normalize_collinear_points("".join(fact)) == norm_diag2
                              for fact in self.collinear_facts)

            if not found_diag1 or not found_diag2:
                missing = []
                if not found_diag1:
                    missing.append(diag1_expected)
                if not found_diag2:
                    missing.append(diag2_expected)
                return return_error(GeometricError(
                    tier=ErrorTier.TIER2_PREMISE_VIOLATION,
                    message=f"Expected collinear fact(s) {', '.join(missing)} not found.",
                    details=f"Stored collinear facts: {[''.join(f) for f in self.collinear_facts]}"
                ))

            return True, None




        elif theorem_name == "circle_property_circular_power_tangent_and_segment_line":
            # Expected arguments: version, token1, token2, token3.
            # For example: (1, "DC", "DBF", "E")
            version = args[0]

            if version !="1":  # Updated to include version "2"
                return return_error(GeometricError(
                    tier=ErrorTier.TIER1_THEOREM_CALL_SYNTAX_VIOLATION,
                    message="these is no such version for the theorem",
                    details="these is no such version for the theorem circle_property_circular_power_tangent_and_segment_line"
                ))
            token1 = args[1].strip()  # e.g., "DC"
            token2 = args[2].strip()  # e.g., "DBF"  (assumed to be a three–letter string)
            token3 = args[3].strip()  # e.g., "E"

            # --- Check that the tangent fact has been recorded.
            if (token1, token3) not in self.tangent_facts:
                return return_error(GeometricError(
                    tier=ErrorTier.TIER2_PREMISE_VIOLATION,
                    message=f"Tangent fact IsTangentOfCircle({token1},{token3}) not found in accumulated data.",
                    details=f"Stored tangent facts: {self.tangent_facts}"
                ))

            # --- Check that a cocircular fact exists for the chord.
            # For token2, we interpret the chord as token2[1:].
            chord = token2[1:]
            found_cocircular = False
            for fact in self.cocircular_facts:
                # Each cocircular fact is assumed to be stored as a tuple whose first element is the center.
                # Compare the sorted list of chord letters with the sorted version of fact[1:].
                if fact[0] == token3 and sorted(fact[1:]) == sorted(list(chord)):
                    found_cocircular = True
                    break
            if not found_cocircular:
                return return_error(GeometricError(
                    tier=ErrorTier.TIER2_PREMISE_VIOLATION,
                    message=f"Expected cocircular fact with center {token3} and chord {chord} not found.",
                    details=f"Stored cocircular facts: {self.cocircular_facts}"
                ))

            # --- Check that the secant is recorded as collinear.
            # We expect a collinear fact corresponding to token2.
            normalized_secant = self.normalize_collinear_points(token2)
            found_collinear = False
            for fact in self.collinear_facts:
                if self.normalize_collinear_points("".join(fact)) == normalized_secant:
                    found_collinear = True
                    break
            if not found_collinear:
                return return_error(GeometricError(
                    tier=ErrorTier.TIER2_PREMISE_VIOLATION,
                    message=f"Expected collinear fact Collinear({token2}) not found.",
                    details=f"Stored collinear facts: {[''.join(f) for f in self.collinear_facts]}"
                ))
            return True, None





        elif theorem_name == "parallel_property_collinear_extend":

            # Validate that the expected collinear fact is present and that the parallel relation exists.

            version = args[0].strip()

            if version not in {"1", "2", "3"}:  # Updated to include version "2"

                return return_error(GeometricError(
                    tier=ErrorTier.TIER1_THEOREM_CALL_SYNTAX_VIOLATION,
                    message="these is no such version for the theorem",
                    details="these is no such version for the theorem parallel_property_collinear_extend"
                ))

            token1 = args[1].strip()  # e.g., "GA"

            token2 = args[2].strip()  # e.g., "HD"

            token3 = args[3].strip()  # e.g., "J"

            # Determine the expected collinear fact from the tokens.

            if version == "1":

                # Expected: token3 + token1

                expected_collinear = token3 + token1

            elif version == "2":

                # Expected: token1 + token3 (ABM)

                expected_collinear = token1 + token3

            elif version == "3":

                # Expected: token1[0] + token3 + token1[1] (AMB)

                expected_collinear = token1[0] + token3 + token1[1]

            normalized_expected = self.normalize_collinear_points(expected_collinear)

            found_collinear = False

            for fact in self.collinear_facts:

                # Assume each fact is stored as a list of points; join them and normalize.

                normalized_fact = self.normalize_collinear_points("".join(fact))

                if normalized_fact == normalized_expected:
                    found_collinear = True

                    break

            if not found_collinear:
                return return_error(GeometricError(

                    tier=ErrorTier.TIER2_PREMISE_VIOLATION,

                    message=f"Expected collinear fact Collinear({expected_collinear}) not found.",

                    details=f"Stored collinear facts: {[''.join(f) for f in self.collinear_facts]}"

                ))

            # Check that a parallel relation between token1 and token2 already exists.

            found_parallel = False

            possible_parallel = {

                (token1, token2),

                (token1[::-1], token2),

                (token1, token2[::-1]),

                (token1[::-1], token2[::-1])

            }

            for pair in self.parallel_pairs:

                if pair in possible_parallel or pair[::-1] in possible_parallel:
                    found_parallel = True

                    break

            if not found_parallel:
                return return_error(GeometricError(

                    tier=ErrorTier.TIER2_PREMISE_VIOLATION,

                    message=f"Expected parallel relation ParallelBetweenLine({token1},{token2}) not found.",

                    details=f"Stored parallel pairs: {self.parallel_pairs}"

                ))

            # If all checks pass, return success.

            return True, None





        elif theorem_name == "circle_property_circular_power_segment_and_segment_line":
            # Expected arguments: version, token1, token2, token3.
            # For example: (1, "AFB", "AGC", "E")
            version = args[0]

            if version != "1":
                return return_error(GeometricError(
                    tier=ErrorTier.TIER1_THEOREM_CALL_SYNTAX_VIOLATION,
                    message="these is no such version for the theorem",
                    details="these is no such version for the theorem circle_property_circular_power_segment_and_segment_line"
                ))  # (unused here but could be used if needed)
            token1 = args[1].strip()  # e.g., "AFB"
            token2 = args[2].strip()  # e.g., "AGC"
            token3 = args[3].strip()  # e.g., "E"

            # --- Check the cocircular facts.
            # For token1, we expect a fact like: Cocircular(E,FB)
            chord1 = token1[1:]  # for "AFB", chord1 = "FB"
            found_cocircular1 = False
            for fact in self.cocircular_facts:
                # Each cocircular fact is stored as a tuple with the center first.
                if fact[0] == token3 and sorted(fact[1:]) == sorted(list(chord1)):
                    found_cocircular1 = True
                    break
            if not found_cocircular1:
                return return_error(GeometricError(
                    tier=ErrorTier.TIER2_PREMISE_VIOLATION,
                    message=f"Expected cocircular fact Cocircular({token3},{chord1}) not found.",
                    details=f"Stored cocircular facts: {self.cocircular_facts}"
                ))

            # For token2, we expect a fact like: Cocircular(E,GC)
            chord2 = token2[1:]  # for "AGC", chord2 = "GC"
            found_cocircular2 = False
            for fact in self.cocircular_facts:
                if fact[0] == token3 and sorted(fact[1:]) == sorted(list(chord2)):
                    found_cocircular2 = True
                    break
            if not found_cocircular2:
                return return_error(GeometricError(
                    tier=ErrorTier.TIER2_PREMISE_VIOLATION,
                    message=f"Expected cocircular fact Cocircular({token3},{chord2}) not found.",
                    details=f"Stored cocircular facts: {self.cocircular_facts}"
                ))

            # --- Check the collinearity facts.
            # Expect Collinear(token1) and Collinear(token2) to be present.
            norm_token1 = self.normalize_collinear_points(token1)
            norm_token2 = self.normalize_collinear_points(token2)
            found_collinear1 = any(self.normalize_collinear_points("".join(fact)) == norm_token1
                                   for fact in self.collinear_facts)
            found_collinear2 = any(self.normalize_collinear_points("".join(fact)) == norm_token2
                                   for fact in self.collinear_facts)
            if not found_collinear1:
                return return_error(GeometricError(
                    tier=ErrorTier.TIER2_PREMISE_VIOLATION,
                    message=f"Expected collinear fact Collinear({token1}) not found.",
                    details=f"Stored collinear facts: {[''.join(f) for f in self.collinear_facts]}"
                ))
            if not found_collinear2:
                return return_error(GeometricError(
                    tier=ErrorTier.TIER2_PREMISE_VIOLATION,
                    message=f"Expected collinear fact Collinear({token2}) not found.",
                    details=f"Stored collinear facts: {[''.join(f) for f in self.collinear_facts]}"
                ))
            return True, None






        elif theorem_name == "radius_of_circle_property_length_equal":

            # Check that the premise includes a centre fact and cocircularity.

            version = args[0]

            if version != "1":
                return return_error(GeometricError(

                    tier=ErrorTier.TIER1_THEOREM_CALL_SYNTAX_VIOLATION,

                    message="these is no such version for the theorem",

                    details="these is no such version for the theorem radius_of_circle_property_length_equal"

                ))

            if len(args) < 3:
                return return_error(GeometricError(

                    tier=ErrorTier.TIER1_THEOREM_CALL_SYNTAX_VIOLATION,

                    message="Insufficient arguments for radius_of_circle_property_length_equal",

                    details="Expected: radius_of_circle_property_length_equal(1, line, circle)"

                ))

            line_token = args[1].strip()  # e.g., "BY"

            circle_token = args[2].strip()  # e.g., "B"

            # Check circle center

            if circle_token not in self.circle_centers:
                return return_error(GeometricError(

                    tier=ErrorTier.TIER2_PREMISE_VIOLATION,

                    message=f"Centre for circle {circle_token} not recorded.",

                    details=f"Accumulated centres: {self.circle_centers}"

                ))

            # Check that IsCentreOfCircle fact is present

            center_match = re.search(
                r'IsCentreOfCircle\(' + re.escape(circle_token) + r',' + re.escape(circle_token) + r'\)', premise)

            if not center_match:
                return return_error(GeometricError(

                    tier=ErrorTier.TIER2_PREMISE_VIOLATION,

                    message=f"Missing IsCentreOfCircle({circle_token},{circle_token}) in premise",

                    details="radius_of_circle_property_length_equal requires center to be defined"

                ))

            # Check Line fact

            line_match = re.search(r'Line\(' + re.escape(line_token) + r'\)', premise)

            if not line_match:
                return return_error(GeometricError(

                    tier=ErrorTier.TIER2_PREMISE_VIOLATION,

                    message=f"Missing Line({line_token}) in premise",

                    details="radius_of_circle_property_length_equal requires line to be defined"

                ))

            # Check Cocircular fact - ensure the endpoint of the line is on the circle

            # For a line BY and circle B, we need Cocircular(B,Y)

            endpoint = line_token[1] if line_token[0] == circle_token else line_token[0]

            cocircular_match = re.search(
                r'Cocircular\(' + re.escape(circle_token) + r',.*' + re.escape(endpoint) + r'.*\)', premise)

            if not cocircular_match:
                return return_error(GeometricError(

                    tier=ErrorTier.TIER2_PREMISE_VIOLATION,

                    message=f"Missing Cocircular({circle_token},...) containing point {endpoint} in premise",

                    details="radius_of_circle_property_length_equal requires line endpoint to be on the circle"

                ))

            # Also check stored cocircular facts

            cocircular_found = False

            for fact in self.cocircular_facts:

                if fact[0] == circle_token and endpoint in fact[1:]:
                    cocircular_found = True

                    break

            if not cocircular_found:
                return return_error(GeometricError(

                    tier=ErrorTier.TIER2_PREMISE_VIOLATION,

                    message=f"Point {endpoint} not proven to be on circle {circle_token}",

                    details=f"Known cocircular facts: {self.cocircular_facts}"

                ))

            # Check that one endpoint of the line is the center of the circle

            if circle_token not in line_token:
                return return_error(GeometricError(

                    tier=ErrorTier.TIER2_PREMISE_VIOLATION,

                    message=f"Line {line_token} does not start or end at circle center {circle_token}",

                    details="For a radius, the line must connect the center to a point on the circle"

                ))

            return True, None


        elif theorem_name == "circle_property_chord_perpendicular_bisect_chord":

            version = args[0].strip()

            if version not in {"1", "2"}:
                return return_error(GeometricError(
                    tier=ErrorTier.TIER1_THEOREM_CALL_SYNTAX_VIOLATION,
                    message="these is no such version for the theorem",
                    details="these is no such version for the theorem circle_property_chord_perpendicular_bisect_chord"
                ))

            if len(args) < 4:
                return return_error(GeometricError(

                    tier=ErrorTier.TIER1_THEOREM_CALL_SYNTAX_VIOLATION,

                    message="Insufficient arguments for circle_property_chord_perpendicular_bisect_chord",

                    details="Expected: circle_property_chord_perpendicular_bisect_chord(version, circle, bisector_line, chord)"

                ))

            circle_token = args[1].strip()  # e.g., "O"

            bisector_line = args[2].strip()  # e.g., "PM"

            chord_token = args[3].strip()  # e.g., "AB"

            # Extract the cocircular fact from the premise

            cocirc_match = re.search(r'Cocircular\(' + re.escape(circle_token) + r',(\w+)\)', premise)

            if not cocirc_match:
                return return_error(GeometricError(

                    tier=ErrorTier.TIER2_PREMISE_VIOLATION,

                    message=f"Missing Cocircular({circle_token},...) fact in premise",

                    details="Required for perpendicular bisector property"

                ))

            points = cocirc_match.group(1)

            # Check if all chord points are in the cocircular set

            if not all(p in points for p in chord_token):
                return return_error(GeometricError(

                    tier=ErrorTier.TIER2_PREMISE_VIOLATION,

                    message=f"Chord points {chord_token} not all in cocircular set {points}",

                    details="All chord points must lie on the circle"

                ))

            # Check against stored cocircular facts

            found = False

            for fact in self.cocircular_facts:

                if fact[0] == circle_token and all(p in ''.join(fact[1:]) for p in chord_token):
                    found = True

                    break

            if not found:
                return return_error(GeometricError(

                    tier=ErrorTier.TIER2_PREMISE_VIOLATION,

                    message=f"Cocircular fact for {circle_token} and points including {chord_token} not established",

                    details=f"Known cocircular facts: {self.cocircular_facts}"

                ))

            # Extract and check collinearity

            midpoint_letter = None

            collinear_match = re.search(r'Collinear\((\w+)\)', premise)

            if collinear_match:

                collinear_points = collinear_match.group(1)

                # Check all chord points are in the collinear set

                if not all(p in collinear_points for p in chord_token):
                    return return_error(GeometricError(

                        tier=ErrorTier.TIER2_PREMISE_VIOLATION,

                        message=f"Not all chord points in collinear set: {chord_token} vs {collinear_points}",

                        details="Chord endpoints must be part of the collinear fact"

                    ))

                # Identify the potential midpoint (point in collinear set not in chord)

                midpoint_candidates = [p for p in collinear_points if p not in chord_token]

                if midpoint_candidates:

                    midpoint_letter = midpoint_candidates[0]

                else:

                    return return_error(GeometricError(

                        tier=ErrorTier.TIER2_PREMISE_VIOLATION,

                        message="Could not identify midpoint from collinear fact",

                        details=f"Collinear points: {collinear_points}, chord: {chord_token}"

                    ))

            else:

                return return_error(GeometricError(

                    tier=ErrorTier.TIER2_PREMISE_VIOLATION,

                    message="Missing collinear fact in premise",

                    details="Required for identifying the chord's midpoint"

                ))

            # Check that the midpoint is on the bisector line

            if midpoint_letter not in bisector_line:
                return return_error(GeometricError(

                    tier=ErrorTier.TIER2_PREMISE_VIOLATION,

                    message=f"Midpoint {midpoint_letter} is not on bisector line {bisector_line}",

                    details="The bisector line must pass through the chord's midpoint"

                ))

            # Check center of circle fact

            center_match = re.search(r'IsCentreOfCircle\((\w+),' + re.escape(circle_token) + r'\)', premise)

            if not center_match:
                return return_error(GeometricError(

                    tier=ErrorTier.TIER2_PREMISE_VIOLATION,

                    message=f"Missing IsCentreOfCircle(...,{circle_token}) fact in premise",

                    details="Required for perpendicular bisector property"

                ))

            center_letter = center_match.group(1)

            # Verify the center is in the bisector line

            if center_letter not in bisector_line:
                return return_error(GeometricError(

                    tier=ErrorTier.TIER2_PREMISE_VIOLATION,

                    message=f"Center {center_letter} is not on bisector line {bisector_line}",

                    details="The bisector line must pass through the center of the circle"

                ))

            # Version-specific checks

            if version == "1":

                # Check for the right angle (perpendicular)

                angle_match = re.search(r'Equal\(MeasureOfAngle\((\w{3})\),90\)', premise)

                if not angle_match:
                    return return_error(GeometricError(

                        tier=ErrorTier.TIER2_PREMISE_VIOLATION,

                        message="Missing right angle fact in premise for version 1",

                        details="Version 1 requires Equal(MeasureOfAngle(...),90)"

                    ))

                angle_name = angle_match.group(1)

                # Verify the angle involves both the midpoint and a chord endpoint

                if midpoint_letter not in angle_name or not any(p in angle_name for p in chord_token):
                    return return_error(GeometricError(

                        tier=ErrorTier.TIER2_PREMISE_VIOLATION,

                        message=f"Right angle {angle_name} does not properly involve chord and midpoint",

                        details=f"Expected an angle including {midpoint_letter} and at least one of {chord_token}"

                    ))


            elif version == "2":

                # Check for equal lengths (bisection)

                length_match = re.search(

                    r'Equal\(LengthOfLine\((\w{2})\),LengthOfLine\((\w{2})\)\)', premise

                )

                if not length_match:
                    return return_error(GeometricError(

                        tier=ErrorTier.TIER2_PREMISE_VIOLATION,

                        message="Missing length equality fact in premise for version 2",

                        details="Version 2 requires Equal(LengthOfLine(...),LengthOfLine(...))"

                    ))

                segment1, segment2 = length_match.groups()

                # Verify these segments represent the two parts of the chord

                valid_segments = False

                for s1, s2 in [(segment1, segment2), (segment2, segment1)]:

                    if (midpoint_letter in s1 and chord_token[0] in s1 and

                            midpoint_letter in s2 and chord_token[1] in s2):
                        valid_segments = True

                        break

                if not valid_segments:
                    return return_error(GeometricError(

                        tier=ErrorTier.TIER2_PREMISE_VIOLATION,

                        message=f"Length equality {segment1}={segment2} doesn't represent chord bisection",

                        details=f"Expected equality between segments {chord_token[0]}{midpoint_letter} and {midpoint_letter}{chord_token[1]}"

                    ))

            return True, None


        elif theorem_name == "midsegment_of_triangle_judgment_parallel":
            version = args[0].strip()
            if version not in {"1", "2", "3"}:
                return return_error(GeometricError(
                    tier=ErrorTier.TIER1_THEOREM_CALL_SYNTAX_VIOLATION,
                    message="these is no such version for the theorem",
                    details="these is no such version for the theorem midsegment_of_triangle_judgment_parallel"
                ))

            if len(args) < 3:
                return return_error(GeometricError(
                    tier=ErrorTier.TIER1_THEOREM_CALL_SYNTAX_VIOLATION,
                    message="Insufficient arguments for midsegment_of_triangle_judgment_parallel",
                    details="Expected: midsegment_of_triangle_judgment_parallel(version, line, triangle)"
                ))

            line = args[1].strip()  # e.g. "DE"
            tri = args[2].strip()  # e.g. "ABC"

            # Check triangle exists
            if self.normalize_triangle(tri) not in self.polygons:
                return return_error(GeometricError(
                    tier=ErrorTier.TIER2_PREMISE_VIOLATION,
                    message=f"Triangle {tri} not defined",
                    details=f"Known polygons: {self.polygons}"
                ))

            # Check for polygon fact
            polygon_match = re.search(r'Polygon\(' + re.escape(tri) + r'\)', premise)
            if not polygon_match:
                return return_error(GeometricError(
                    tier=ErrorTier.TIER2_PREMISE_VIOLATION,
                    message=f"Missing Polygon({tri}) fact in premise",
                    details="Midsegment theorem requires the triangle to be defined"
                ))

            # Extract collinear facts from premise
            collinear_matches = re.findall(r'Collinear\((\w+)\)', premise)
            if len(collinear_matches) < 2:
                return return_error(GeometricError(
                    tier=ErrorTier.TIER2_PREMISE_VIOLATION,
                    message="Missing required collinear points",
                    details="Midsegment theorem requires two collinear facts"
                ))

            # Check each collinear fact against stored facts
            for collinear_points in collinear_matches:
                normalized = self.normalize_collinear_points(collinear_points)
                if not any(self.normalize_collinear_points(''.join(fact)) == normalized
                           for fact in self.collinear_facts):
                    return return_error(GeometricError(
                        tier=ErrorTier.TIER2_PREMISE_VIOLATION,
                        message=f"Points {collinear_points} not proven collinear",
                        details=f"Known collinear facts: {self.collinear_facts}"
                    ))

            # Check for Line fact
            line_match = re.search(r'Line\(' + re.escape(line) + r'\)', premise)
            if not line_match:
                return return_error(GeometricError(
                    tier=ErrorTier.TIER2_PREMISE_VIOLATION,
                    message=f"Missing Line({line}) fact in premise",
                    details="Midsegment theorem requires the line to be defined"
                ))

            # Extract and check parallel fact
            parallel_match = re.search(r'ParallelBetweenLine\(' + re.escape(line) + r',(\w+)\)', premise) or \
                             re.search(r'ParallelBetweenLine\((\w+),' + re.escape(line) + r'\)', premise)
            if not parallel_match:
                return return_error(GeometricError(
                    tier=ErrorTier.TIER2_PREMISE_VIOLATION,
                    message="Missing parallel line relation",
                    details=f"Midsegment theorem requires {line} to be parallel to a side of the triangle"
                ))

            other_line = parallel_match.group(1)
            possible_pairs = [
                (line, other_line),
                (other_line, line),
                (line[::-1], other_line),
                (line, other_line[::-1]),
                (other_line[::-1], line),
                (other_line, line[::-1])
            ]

            if not any(pair in self.parallel_pairs for pair in possible_pairs):
                return return_error(GeometricError(
                    tier=ErrorTier.TIER2_PREMISE_VIOLATION,
                    message=f"Lines {line} and {other_line} not proven parallel",
                    details=f"Known parallel pairs: {self.parallel_pairs}"
                ))

            # Check for the appropriate length equality based on version
            if version == "1":
                # Version 1: Equal(LengthOfLine(AD),LengthOfLine(BD))
                # Need to find the specific length equality matching the pattern
                length_equal_found = False
                for vertex in tri:
                    for endpoint in line:
                        pattern = f"Equal\\(LengthOfLine\\({vertex}{endpoint}\\),LengthOfLine\\(\\w{endpoint}\\)\\)"
                        if re.search(pattern, premise):
                            length_equal_found = True
                            break
                    if length_equal_found:
                        break

                if not length_equal_found:
                    return return_error(GeometricError(
                        tier=ErrorTier.TIER2_PREMISE_VIOLATION,
                        message="Missing length equality for version 1",
                        details="Version 1 requires equal lengths from triangle vertex to midsegment endpoints"
                    ))

            elif version == "2":
                # Version 2: Equal(LengthOfLine(AE),LengthOfLine(CE))
                # Similar pattern matching for the second type of length equality
                length_equal_found = False
                for vertex in tri:
                    for endpoint in line:
                        pattern = f"Equal\\(LengthOfLine\\({vertex}{endpoint}\\),LengthOfLine\\(\\w{endpoint}\\)\\)"
                        if re.search(pattern, premise):
                            length_equal_found = True
                            break
                    if length_equal_found:
                        break

                if not length_equal_found:
                    return return_error(GeometricError(
                        tier=ErrorTier.TIER2_PREMISE_VIOLATION,
                        message="Missing length equality for version 2",
                        details="Version 2 requires equal lengths from triangle vertex to midsegment endpoints"
                    ))

            elif version == "3":
                # Version 3: Equal(LengthOfLine(BC),Mul(LengthOfLine(DE),2))
                length_match = re.search(
                    r'Equal\(LengthOfLine\((\w+)\),Mul\(LengthOfLine\(' + re.escape(line) + r'\),2\)\)', premise)
                if not length_match:
                    return return_error(GeometricError(
                        tier=ErrorTier.TIER2_PREMISE_VIOLATION,
                        message="Missing required length relationship for version 3",
                        details=f"Version 3 requires that a side of the triangle equals twice the length of {line}"
                    ))

            return True, None

        elif theorem_name == "arc_length_formula":
            version = args[0]

            if version != "1":
                return return_error(GeometricError(
                    tier=ErrorTier.TIER1_THEOREM_CALL_SYNTAX_VIOLATION,
                    message="these is no such version for the theorem",
                    details="these is no such version for the theorem arc_length_formula"
                ))
            arc_match = re.search(r'Arc\((\w+)\)', premise)

            if not arc_match:
                return return_error(GeometricError(

                    tier=ErrorTier.TIER2_PREMISE_VIOLATION,

                    message="Missing arc definition"

                ))

            arc_name = arc_match.group(1)

            normalized_arc = self.normalize_arc(arc_name)

            if f"arc_{normalized_arc}" not in self.arcs:
                return return_error(GeometricError(

                    tier=ErrorTier.TIER2_PREMISE_VIOLATION,

                    message=f"Arc {arc_name} not established",

                    details=f"Known arcs: {list(self.arcs.keys())}"

                ))

            return True, None


        elif theorem_name == "arc_property_circumference_angle_internal":
            # Extract angle from premise
            version = args[0]

            if version != "1":
                return return_error(GeometricError(
                    tier=ErrorTier.TIER1_THEOREM_CALL_SYNTAX_VIOLATION,
                    message="these is no such version for the theorem",
                    details="these is no such version for the theorem arc_property_circumference_angle_internal"
                ))
            angle_match = re.search(r'Angle\((\w{3})\)', premise)
            if not angle_match:
                return return_error(GeometricError(
                    tier=ErrorTier.TIER2_PREMISE_VIOLATION,
                    message="Missing angle in premise"
                ))

            return True, None


        elif theorem_name == "parallel_property_ipsilateral_internal_angle":

            # Extract angle from premise
            version = args[0]

            if version != "1":
                return return_error(GeometricError(
                    tier=ErrorTier.TIER1_THEOREM_CALL_SYNTAX_VIOLATION,
                    message="these is no such version for the theorem",
                    details="these is no such version for the theorem parallel_property_ipsilateral_internal_angle"
                ))

            # The premise should include a ParallelBetweenLine clause and a Line clause.
            parallel_match = re.search(r'ParallelBetweenLine\((\w+),(\w+)\)', premise)
            if not parallel_match:
                return return_error(GeometricError(
                    tier=ErrorTier.TIER2_PREMISE_VIOLATION,
                    message="Missing parallel lines in premise"
                ))

            line1, line2 = parallel_match.groups()
            # Check against stored parallel pairs
            possible_pairs = (line1, line2)

            if not possible_pairs in self.parallel_pairs:
                return return_error(GeometricError(
                    tier=ErrorTier.TIER2_PREMISE_VIOLATION,
                    message=f"Lines {line1} and {line2} not proven parallel",
                    details=f"Known parallel pairs: {self.parallel_pairs}"
                ))
            return True, None


        elif theorem_name == "circle_property_circular_power_segment_and_segment_angle":

            # Extract the cocircular fact tokens from the premise.
            version = args[0]

            if version not in ["1","2"]:
                return return_error(GeometricError(
                    tier=ErrorTier.TIER1_THEOREM_CALL_SYNTAX_VIOLATION,
                    message="these is no such version for the theorem",
                    details="these is no such version for the theorem circle_property_circular_power_segment_and_segment_angle"
                ))
            cocirc_match = re.search(r'Cocircular\((\w),(\w+)\)', premise)

            if not cocirc_match:
                return return_error(GeometricError(

                    tier=ErrorTier.TIER2_PREMISE_VIOLATION,

                    message="Premise is missing a valid Cocircular(...) fact.",

                    details=f"Premise provided: {premise}"

                ))

            circle_token, arc_group_token = cocirc_match.groups()  # e.g. 'B' and 'SUVT'

            # Check generically: for each stored cocircular fact (stored as a tuple),

            # see if the first element equals the circle token and the remaining elements,

            # when sorted, match the sorted list of letters in the arc group.

            found = False

            for fact in self.cocircular_facts:

                # fact is a tuple like ('B', 'S', 'U', 'V', 'T')—or possibly in some order.

                if fact[0] == circle_token and sorted(fact[1:]) == sorted(list(arc_group_token)):
                    found = True

                    break

            if not found:
                return return_error(GeometricError(

                    tier=ErrorTier.TIER2_PREMISE_VIOLATION,

                    message=f"Cocircular({circle_token},{arc_group_token}) not established",

                    details=f"Accumulated cocircular facts: {self.cocircular_facts}"

                ))

            # Similarly, do a generic check for the collinear facts.

            # For example, if the theorem call also requires Collinear(RST):

            collinear_match1 = re.search(r'Collinear\((\w+)\)', premise)

            if collinear_match1:

                collinear_token = collinear_match1.group(1)

                found_coll = any(
                    self.normalize_collinear_points(''.join(fact)) == self.normalize_collinear_points(collinear_token)

                    for fact in self.collinear_facts)

                if not found_coll:
                    return return_error(GeometricError(

                        tier=ErrorTier.TIER2_PREMISE_VIOLATION,

                        message=f"Collinear({collinear_token}) not established",

                        details=f"Known collinear facts: {self.collinear_facts}"

                    ))

            # (Repeat as needed for any additional required collinear facts.)

            return True, None





        elif theorem_name == "triangle_perimeter_formula":
            # Check that the premise contains a valid triangle.
            # Expecting something like: Polygon(ABC)
            version = args[0]

            if version != "1":
                return return_error(GeometricError(
                    tier=ErrorTier.TIER1_THEOREM_CALL_SYNTAX_VIOLATION,
                    message="these is no such version for the theorem",
                    details="these is no such version for the theorem triangle_perimeter_formula"
                ))
            poly_match = re.search(r'Polygon\((\w+)\)', premise)
            if not poly_match:
                return return_error(GeometricError(
                    tier=ErrorTier.TIER2_PREMISE_VIOLATION,
                    message="Missing or invalid Polygon() in premise for sine_theorem"
                ))
            return True, None




        elif theorem_name == "tangent_of_circle_property_perpendicular":

            # Expected premise (from the theorem‐sequence) is something like:

            # "IsTangentOfCircle(AN,O)&Angle(ANO)&IsCentreOfCircle(O,O)"

            # Instead of merely checking for substring membership, we extract and then check

            # that these facts have already been accumulated.

            # Check for the tangent fact.
            version = args[0]

            if version not in  ["1","2"]:
                return return_error(GeometricError(
                    tier=ErrorTier.TIER1_THEOREM_CALL_SYNTAX_VIOLATION,
                    message="these is no such version for the theorem",
                    details="these is no such version for the theorem tangent_of_circle_property_perpendicular"
                ))

            tan_m = re.search(r'IsTangentOfCircle\((\w+),(\w+)\)', premise)

            if not tan_m:
                return return_error(GeometricError(

                    tier=ErrorTier.TIER2_PREMISE_VIOLATION,

                    message="Missing IsTangentOfCircle(...) in premise for tangent_of_circle_property_perpendicular",

                    details=f"Premise provided: {premise}"

                ))

            tangent_line_from_premise, center_from_tangent = tan_m.group(1), tan_m.group(2)

            if (tangent_line_from_premise, center_from_tangent) not in self.tangent_facts:
                return return_error(GeometricError(

                    tier=ErrorTier.TIER2_PREMISE_VIOLATION,

                    message=f"Tangent fact IsTangentOfCircle({tangent_line_from_premise},{center_from_tangent}) not established",

                    details=f"Accumulated tangent facts: {self.tangent_facts}"

                ))

            # Check for an angle fact.

            angle_m = re.search(r'Angle\((\w{3})\)', premise)

            if not angle_m:
                return return_error(GeometricError(

                    tier=ErrorTier.TIER2_PREMISE_VIOLATION,

                    message="Missing Angle(...) in premise for tangent_of_circle_property_perpendicular",

                    details=f"Premise provided: {premise}"

                ))

            angle_str = angle_m.group(1)

            normalized_angle = self.normalize_angle_name(angle_str)

            # Check for the centre fact.

            centre_m = re.search(r'IsCentreOfCircle\((\w+),(\w+)\)', premise)

            if not centre_m:
                return return_error(GeometricError(

                    tier=ErrorTier.TIER2_PREMISE_VIOLATION,

                    message="Missing IsCentreOfCircle(...) in premise for tangent_of_circle_property_perpendicular",

                    details=f"Premise provided: {premise}"

                ))

            centre_from_fact = centre_m.group(1)

            if centre_from_fact not in self.circle_centers:
                return return_error(GeometricError(

                    tier=ErrorTier.TIER2_PREMISE_VIOLATION,

                    message=f"Centre {centre_from_fact} not established",

                    details=f"Accumulated centres: {self.circle_centers}"

                ))

            return True, None


        elif theorem_name == "arc_property_center_angle":
            version = args[0]

            if version != "1":
                return return_error(GeometricError(
                    tier=ErrorTier.TIER1_THEOREM_CALL_SYNTAX_VIOLATION,
                    message="these is no such version for the theorem",
                    details="these is no such version for the theorem arc_property_center_angle"
                ))
            # Expected premise: e.g. "Arc(OMN)&Angle(NOM)&IsCentreOfCircle(O,O)"

            # Extract the arc fact.

            arc_m = re.search(r'Arc\((\w{3})\)', premise)

            if not arc_m:
                return return_error(GeometricError(

                    tier=ErrorTier.TIER2_PREMISE_VIOLATION,

                    message="Missing Arc(...) in premise for arc_property_center_angle",

                    details=f"Premise provided: {premise}"

                ))

            arc_name = arc_m.group(1)

            normalized_arc = self.normalize_arc(arc_name)

            if f"arc_{normalized_arc}" not in self.arcs:
                return return_error(GeometricError(

                    tier=ErrorTier.TIER2_PREMISE_VIOLATION,

                    message=f"Arc {arc_name} not established",

                    details=f"Accumulated arcs: {list(self.arcs.keys())}"

                ))

            # Check for an angle fact.

            angle_m = re.search(r'Angle\((\w{3})\)', premise)

            if not angle_m:
                return return_error(GeometricError(

                    tier=ErrorTier.TIER2_PREMISE_VIOLATION,

                    message="Missing Angle(...) in premise for arc_property_center_angle",

                    details=f"Premise provided: {premise}"

                ))

            angle_str = angle_m.group(1)

            normalized_angle = self.normalize_angle_name(angle_str)

            # Check for the centre fact.

            centre_m = re.search(r'IsCentreOfCircle\((\w+),(\w+)\)', premise)

            if not centre_m:
                return return_error(GeometricError(

                    tier=ErrorTier.TIER2_PREMISE_VIOLATION,

                    message="Missing IsCentreOfCircle(...) in premise for arc_property_center_angle",

                    details=f"Premise provided: {premise}"

                ))

            centre_from_fact = centre_m.group(1)

            if centre_from_fact not in self.circle_centers:
                return return_error(GeometricError(

                    tier=ErrorTier.TIER2_PREMISE_VIOLATION,

                    message=f"Centre {centre_from_fact} not established",

                    details=f"Accumulated centres: {self.circle_centers}"

                ))

            return True, None


        elif theorem_name == "arc_property_circumference_angle_external":
            version = args[0]

            if version != "1":
                return return_error(GeometricError(
                    tier=ErrorTier.TIER1_THEOREM_CALL_SYNTAX_VIOLATION,
                    message="these is no such version for the theorem",
                    details="these is no such version for the theorem arc_property_circumference_angle_external"
                ))
            # Expected premise: e.g. "Cocircular(O,MNB)&Angle(NBM)"

            # Extract the cocircular fact.

            cocirc_m = re.search(r'Cocircular\((\w+),(\w+)\)', premise)

            if not cocirc_m:
                return return_error(GeometricError(

                    tier=ErrorTier.TIER2_PREMISE_VIOLATION,

                    message="Missing Cocircular(...) in premise for arc_property_circumference_angle_external",

                    details=f"Premise provided: {premise}"

                ))

            circle_from_cocirc = cocirc_m.group(1)

            points_str = cocirc_m.group(2)

            found = False

            for fact in self.cocircular_facts:

                # Assume each cocircular fact is stored as a tuple with the circle as first element

                # and the remaining letters as the points on the circle.

                if fact[0] == circle_from_cocirc and sorted(fact[1:]) == sorted(list(points_str)):
                    found = True

                    break

            if not found:
                return return_error(GeometricError(

                    tier=ErrorTier.TIER2_PREMISE_VIOLATION,

                    message=f"Cocircular({circle_from_cocirc},{points_str}) not established",

                    details=f"Accumulated cocircular facts: {self.cocircular_facts}"

                ))

            # Check for an angle fact.

            angle_m = re.search(r'Angle\((\w{3})\)', premise)

            if not angle_m:
                return return_error(GeometricError(

                    tier=ErrorTier.TIER2_PREMISE_VIOLATION,

                    message="Missing Angle(...) in premise for arc_property_circumference_angle_external",

                    details=f"Premise provided: {premise}"

                ))

            angle_str = angle_m.group(1)

            normalized_angle = self.normalize_angle_name(angle_str)

            # if f"angle_{normalized_angle}" not in self.angles:
            #     return return_error(GeometricError(
            #
            #         tier=ErrorTier.TIER2_PREMISE_VIOLATION,
            #
            #         message=f"Angle {angle_str} not established",
            #
            #         details=f"Accumulated angles: {list(self.angles.keys())}"
            #
            #     ))

            return True, None



        elif theorem_name == "arc_property_center_angle":
            version = args[0]

            if version != "1":
                return return_error(GeometricError(
                    tier=ErrorTier.TIER1_THEOREM_CALL_SYNTAX_VIOLATION,
                    message="these is no such version for the theorem",
                    details="these is no such version for the theorem arc_property_center_angle"
                ))
            # Expected premise: e.g. "Arc(OMN)&Angle(NOM)&IsCentreOfCircle(O,O)"

            # Extract the arc fact.

            arc_m = re.search(r'Arc\((\w{3})\)', premise)

            if not arc_m:
                return return_error(GeometricError(

                    tier=ErrorTier.TIER2_PREMISE_VIOLATION,

                    message="Missing Arc(...) in premise for arc_property_center_angle",

                    details=f"Premise provided: {premise}"

                ))

            arc_name = arc_m.group(1)

            normalized_arc = self.normalize_arc(arc_name)

            if f"arc_{normalized_arc}" not in self.arcs:
                return return_error(GeometricError(

                    tier=ErrorTier.TIER2_PREMISE_VIOLATION,

                    message=f"Arc {arc_name} not established",

                    details=f"Accumulated arcs: {list(self.arcs.keys())}"

                ))

            # Check for an angle fact.

            angle_m = re.search(r'Angle\((\w{3})\)', premise)

            if not angle_m:
                return return_error(GeometricError(

                    tier=ErrorTier.TIER2_PREMISE_VIOLATION,

                    message="Missing Angle(...) in premise for arc_property_center_angle",

                    details=f"Premise provided: {premise}"

                ))

            angle_str = angle_m.group(1)

            normalized_angle = self.normalize_angle_name(angle_str)

            if f"angle_{normalized_angle}" not in self.angles:
                return return_error(GeometricError(

                    tier=ErrorTier.TIER2_PREMISE_VIOLATION,

                    message=f"Angle {angle_str} not established",

                    details=f"Accumulated angles: {list(self.angles.keys())}"

                ))

            # Check for the centre fact.

            centre_m = re.search(r'IsCentreOfCircle\((\w+),(\w+)\)', premise)

            if not centre_m:
                return return_error(GeometricError(

                    tier=ErrorTier.TIER2_PREMISE_VIOLATION,

                    message="Missing IsCentreOfCircle(...) in premise for arc_property_center_angle",

                    details=f"Premise provided: {premise}"

                ))

            centre_from_fact = centre_m.group(1)

            if centre_from_fact not in self.circle_centers:
                return return_error(GeometricError(

                    tier=ErrorTier.TIER2_PREMISE_VIOLATION,

                    message=f"Centre {centre_from_fact} not established",

                    details=f"Accumulated centres: {self.circle_centers}"

                ))

            return True, None


        elif theorem_name == "arc_property_circumference_angle_external":
            version = args[0]

            if version != "1":
                return return_error(GeometricError(
                    tier=ErrorTier.TIER1_THEOREM_CALL_SYNTAX_VIOLATION,
                    message="these is no such version for the theorem",
                    details="these is no such version for the theorem arc_property_circumference_angle_external"
                ))
            # Expected premise: e.g. "Cocircular(O,MNB)&Angle(NBM)"

            # Extract the cocircular fact.

            cocirc_m = re.search(r'Cocircular\((\w+),(\w+)\)', premise)

            if not cocirc_m:
                return return_error(GeometricError(

                    tier=ErrorTier.TIER2_PREMISE_VIOLATION,

                    message="Missing Cocircular(...) in premise for arc_property_circumference_angle_external",

                    details=f"Premise provided: {premise}"

                ))

            circle_from_cocirc = cocirc_m.group(1)

            points_str = cocirc_m.group(2)

            found = False

            for fact in self.cocircular_facts:

                # Assume each cocircular fact is stored as a tuple with the circle as first element

                # and the remaining letters as the points on the circle.

                if fact[0] == circle_from_cocirc and sorted(fact[1:]) == sorted(list(points_str)):
                    found = True

                    break

            if not found:
                return return_error(GeometricError(

                    tier=ErrorTier.TIER2_PREMISE_VIOLATION,

                    message=f"Cocircular({circle_from_cocirc},{points_str}) not established",

                    details=f"Accumulated cocircular facts: {self.cocircular_facts}"

                ))

            # Check for an angle fact.

            angle_m = re.search(r'Angle\((\w{3})\)', premise)

            if not angle_m:
                return return_error(GeometricError(

                    tier=ErrorTier.TIER2_PREMISE_VIOLATION,

                    message="Missing Angle(...) in premise for arc_property_circumference_angle_external",

                    details=f"Premise provided: {premise}"

                ))

            angle_str = angle_m.group(1)

            normalized_angle = self.normalize_angle_name(angle_str)

            if f"angle_{normalized_angle}" not in self.angles:
                return return_error(GeometricError(

                    tier=ErrorTier.TIER2_PREMISE_VIOLATION,

                    message=f"Angle {angle_str} not established",

                    details=f"Accumulated angles: {list(self.angles.keys())}"

                ))

            return True, None






        elif theorem_name == "sine_theorem":
            # Check that the premise contains a valid triangle.
            # Expecting something like: Polygon(ABC)
            version = args[0]
            if version != "1":
                return return_error(GeometricError(
                    tier=ErrorTier.TIER1_THEOREM_CALL_SYNTAX_VIOLATION,
                    message="these is no such version for the theorem",
                    details="these is no such version for the theorem sine_theorem"
                ))
            poly_match = re.search(r'Polygon\((\w+)\)', premise)
            if not poly_match:
                return return_error(GeometricError(
                    tier=ErrorTier.TIER2_PREMISE_VIOLATION,
                    message="Missing or invalid Polygon() in premise for sine_theorem"
                ))
            triangle_points = poly_match.group(1)
            if len(triangle_points) != 3:
                return return_error(GeometricError(
                    tier=ErrorTier.TIER2_PREMISE_VIOLATION,
                    message=f"Polygon({triangle_points}) does not represent a triangle (3 vertices expected)"
                ))
            # Optionally, if the theorem call provides a triangle (as args[1]),
            # verify that it matches the Polygon fact.
            if len(args) >= 2 and args[1].strip() != triangle_points:
                return return_error(GeometricError(
                    tier=ErrorTier.TIER2_PREMISE_VIOLATION,
                    message=f"Polygon in premise ({triangle_points}) does not match the triangle in theorem call ({args[1].strip()})"
                ))
            return True, None


        elif theorem_name == "diameter_of_circle_property_right_angle":
            # premise typically: IsDiameterOfCircle(BA,D)&Cocircular(DBCA)&Angle(BCA)
            # 1) Check IsDiameterOfCircle(BA,D) is among our is_diameter_of_circle
            # 2) Check Cocircular(DBCA) is in self.cocircular_facts
            # 3) Check 'Angle(BCA)' => just means that angle is recognized
            # If any fail -> Tier2 premise error
            version = args[0]
            if version != "1":
                return return_error(GeometricError(
                    tier=ErrorTier.TIER1_THEOREM_CALL_SYNTAX_VIOLATION,
                    message="these is no such version for the theorem",
                    details="these is no such version for the theorem diameter_of_circle_property_right_angle"
                ))

            # 1) check diameter premise
            diam_m = re.search(r'IsDiameterOfCircle\((\w+),(\w+)\)', premise)
            if not diam_m:
                return return_error(GeometricError(
                    tier=ErrorTier.TIER2_PREMISE_VIOLATION,
                    message="Missing or invalid IsDiameterOfCircle(...) in premise"
                ))
            line_name, circle_name = diam_m.groups()
            # see if (line_name, circle_name) is in self.is_diameter_of_circle
            if (line_name, circle_name) not in self.is_diameter_of_circle and (
                    line_name[::-1], circle_name) not in self.is_diameter_of_circle:
                return return_error(GeometricError(
                    tier=ErrorTier.TIER2_PREMISE_VIOLATION,
                    message=f"Line {line_name} is not recorded as a diameter of circle {circle_name}"
                ))

            # 2) check Cocircular(...) e.g. Cocircular(DBCA)
            # 2) check Cocircular(...) e.g. Cocircular(D,BCA)
            cocirc_m = re.search(r'Cocircular\((\w+),(\w+)\)', premise)
            if not cocirc_m:
                return return_error(GeometricError(
                    tier=ErrorTier.TIER2_PREMISE_VIOLATION,
                    message="Missing Cocircular(...) in premise"
                ))
            circle_from_cocirc, points_str = cocirc_m.groups()
            # For example, for "Cocircular(D,BCA)" we have circle_from_cocirc == "D" and points_str == "BCA"
            # Now check if a matching cocircular fact exists.
            found_cocirc = False
            for ctuple in self.cocircular_facts:
                # Assume that each cocircular fact is stored as a tuple with the circle as first element
                # For example, a stored fact might be ('D', 'B', 'C', 'A')
                if ctuple[0] == circle_from_cocirc and len(ctuple) == len(points_str) + 1:
                    # Compare the remaining points in a sorted way so that the order doesn't matter.
                    if sorted(ctuple[1:]) == sorted(points_str):
                        found_cocirc = True
                        break
            if not found_cocirc:
                return return_error(GeometricError(
                    tier=ErrorTier.TIER2_PREMISE_VIOLATION,
                    message=f"Cocircular({circle_from_cocirc},{points_str}) was not established"
                ))

            # 3) check "Angle(BCA)" or similar
            angle_m = re.search(r'Angle\((\w+)\)', premise)
            if not angle_m:
                return return_error(GeometricError(
                    tier=ErrorTier.TIER2_PREMISE_VIOLATION,
                    message="Missing Angle(...) in premise"
                ))
            # If all good:
            return True, None





        elif theorem_name == "right_triangle_property_pythagorean":
            version = args[0]
            if version == "1":
                # Expecting a theorem call like: right_triangle_property_pythagorean(1, GHE)

                # and that the triangle has already been recorded as a right triangle.

                if len(args) < 2:
                    return return_error(GeometricError(

                        tier=ErrorTier.TIER1_THEOREM_CALL_SYNTAX_VIOLATION,

                        message="Missing triangle argument for right_triangle_property_pythagorean",

                        details="Expected right_triangle_property_pythagorean(1, triangle)"

                    ))

                triangle = args[1].strip()

                # Instead of scanning the premise string, check the recorded right triangles.

                if self.normalize_triangle(triangle) not in self.right_triangles:
                    return return_error(GeometricError(

                        tier=ErrorTier.TIER2_PREMISE_VIOLATION,

                        message=f"RightTriangle({triangle}) is not recorded.",

                        details=f"Recorded right triangles: {self.right_triangles}"

                    ))

                return True, None
            else:
                return return_error(GeometricError(
                    tier=ErrorTier.TIER1_THEOREM_CALL_SYNTAX_VIOLATION,
                    message="these is no such version for the theorem",
                    details="these is no such version for the theorem right_triangle_property_pythagorean"
                ))





        elif theorem_name == "triangle_area_formula_sine":
            # premise example: Polygon(CAB)
            # conclusion: "Equal(AreaOfTriangle(CAB),Mul(LengthOfLine(CA),LengthOfLine(CB),Sin(MeasureOfAngle(ACB)),1/2))"
            # Just check premise has "Polygon(CAB)"
            version = args[0]
            if version != "1":
                return return_error(GeometricError(
                    tier=ErrorTier.TIER1_THEOREM_CALL_SYNTAX_VIOLATION,
                    message="these is no such version for the theorem",
                    details="these is no such version for the theorem triangle_area_formula_sine"
                ))

            pm = re.search(r'Polygon\((\w+)\)', premise)
            if not pm:
                return return_error(GeometricError(
                    tier=ErrorTier.TIER2_PREMISE_VIOLATION,
                    message="triangle_area_formula_sine requires Polygon(...) in premise"
                ))
            # That’s enough for a basic Tier2 check
            return True, None

        elif theorem_name == "diameter_of_circle_property_length_equal":
            # premise: "IsDiameterOfCircle(BA,D)"
            # conclusion: "Equal(LengthOfLine(BA),DiameterOfCircle(D))"
            version = args[0]
            if version != "1":
                return return_error(GeometricError(
                    tier=ErrorTier.TIER1_THEOREM_CALL_SYNTAX_VIOLATION,
                    message="these is no such version for the theorem",
                    details="these is no such version for the theorem diameter_of_circle_property_length_equal"
                ))
            diam_m = re.search(r'IsDiameterOfCircle\((\w+),(\w+)\)', premise)
            if not diam_m:
                return return_error(GeometricError(
                    tier=ErrorTier.TIER2_PREMISE_VIOLATION,
                    message="Missing IsDiameterOfCircle(...) in premise"
                ))
            line_name, circle_name = diam_m.groups()
            if (line_name, circle_name) not in self.is_diameter_of_circle and (
                    line_name[::-1], circle_name) not in self.is_diameter_of_circle:
                return return_error(GeometricError(
                    tier=ErrorTier.TIER2_PREMISE_VIOLATION,
                    message=f"Line {line_name} is not recorded as diameter of circle {circle_name}"
                ))
            return True, None

        elif theorem_name == "circle_property_length_of_radius_and_diameter":
            # premise: "Circle(D)"
            # conclusion: "Equal(DiameterOfCircle(D),Mul(RadiusOfCircle(D),2))"
            version = args[0]
            if version != "1":
                return return_error(GeometricError(
                    tier=ErrorTier.TIER1_THEOREM_CALL_SYNTAX_VIOLATION,
                    message="these is no such version for the theorem",
                    details="these is no such version for the theorem circle_property_length_of_radius_and_diameter"
                ))
            circ_m = re.search(r'Circle\((\w+)\)', premise)
            if not circ_m:
                return return_error(GeometricError(
                    tier=ErrorTier.TIER2_PREMISE_VIOLATION,
                    message="Missing Circle(...) in premise"
                ))
            circle_name = circ_m.group(1)
            if circle_name not in self.circle_radii:
                return return_error(GeometricError(
                    tier=ErrorTier.TIER2_PREMISE_VIOLATION,
                    message=f"Circle {circle_name} not known"
                ))
            return True, None

        elif theorem_name == "circle_area_formula":
            version = args[0]
            if version != "1":
                return return_error(GeometricError(
                    tier=ErrorTier.TIER1_THEOREM_CALL_SYNTAX_VIOLATION,
                    message="these is no such version for the theorem",
                    details="these is no such version for the theorem circle_area_formula"
                ))
            # premise: "Circle(D)"
            # conclusion: "Equal(AreaOfCircle(D),Mul(pi,RadiusOfCircle(D),RadiusOfCircle(D)))"
            circ_m = re.search(r'Circle\((\w+)\)', premise)
            if not circ_m:
                return return_error(GeometricError(
                    tier=ErrorTier.TIER2_PREMISE_VIOLATION,
                    message="Missing Circle(...) in premise for circle_area_formula"
                ))
            circle_name = circ_m.group(1)
            if circle_name not in self.circle_radii:
                return return_error(GeometricError(
                    tier=ErrorTier.TIER2_PREMISE_VIOLATION,
                    message=f"Circle {circle_name} is not declared"
                ))
            return True, None





        elif theorem_name == "right_triangle_judgment_angle":
            # Expecting something like: "Polygon(GHE)&Equal(MeasureOfAngle(GHE),90)"
            version = args[0]
            if version == "1":
                if len(args) < 2:
                    return return_error(GeometricError(
                        tier=ErrorTier.TIER1_THEOREM_CALL_SYNTAX_VIOLATION,
                        message="Missing triangle argument for right_triangle_judgment_angle",
                        details="Expected right_triangle_judgment_angle(1, triangle)"
                    ))
                triangle = args[1].strip()
                # Check that a Polygon fact exists for this triangle.
                polygon_found = False
                # Also check that an angle measure equality specifying 90° is present.
                angle_90_found = False
                # Split the premise on '&' to get the individual facts.
                for conj in premise.split('&'):
                    conj = conj.strip()
                    # Check for the polygon fact:
                    if conj.startswith("Polygon("):
                        m_poly = re.match(r'Polygon\((\w+)\)', conj)
                        if m_poly:
                            poly_name = m_poly.group(1)
                            # Normalize both names so that e.g. "GHE" and "HEG" are equivalent.
                            if self.normalize_triangle(poly_name) in self.polygons:
                                polygon_found = True
                    # Check for the angle equality specifying 90°
                    elif conj.startswith("Equal(MeasureOfAngle("):
                        m_angle = re.match(r'Equal\(MeasureOfAngle\((\w+)\),\s*(\d+)\)', conj)
                        if m_angle:
                            angle_str = m_angle.group(1)
                            angle_val = int(m_angle.group(2))

                            # Check if this angle is related to the triangle
                            if any(p in angle_str for p in triangle):
                                # Get or create the angle variable
                                angle_var = self.add_angle(angle_str[0], angle_str[1], angle_str[2])

                                # Check if angle is constrained to be 90 in the Z3 model
                                if self.solver.check() == sat:
                                    temp_solver = Solver()
                                    for c in self.solver.assertions():
                                        temp_solver.add(c)

                                    # Try to find a solution where the angle is not 90
                                    temp_solver.add(angle_var != 90)

                                    if temp_solver.check() == unsat:
                                        # If unsatisfiable, the angle must be exactly 90
                                        angle_90_found = True
                                        print(
                                            f"Verified angle {angle_str} is constrained to be 90 degrees in the model.")
                                    else:
                                        # The angle could be something other than 90
                                        alt_model = temp_solver.model()
                                        alt_val = float(alt_model.eval(angle_var).as_decimal(10).rstrip('?'))
                                        print(
                                            f"Warning: Angle {angle_str} is not constrained to be 90 degrees. Could also be {alt_val}.")
                                else:
                                    print(f"Warning: Solver is unsatisfiable when checking angle {angle_str}.")
                # if not polygon_found:
                #     return return_error(GeometricError(
                #         tier=ErrorTier.TIER2_PREMISE_VIOLATION,
                #         message=f"Polygon fact for triangle {triangle} is missing in the premise.",
                #         details=f"Premise provided: {premise}"
                #     ))
                if not angle_90_found:
                    return return_error(GeometricError(
                        tier=ErrorTier.TIER2_PREMISE_VIOLATION,
                        message=f"Angle measure 90° for triangle {triangle} is not established in the premise.",
                        details=f"Premise provided: {premise}"
                    ))
                return True, None
            else:
                return return_error(GeometricError(
                    tier=ErrorTier.TIER1_THEOREM_CALL_SYNTAX_VIOLATION,
                    message="these is no such version for the theorem",
                    details="these is no such version for the theorem right_triangle_judgment_angle"
                ))



        elif theorem_name == "triangle_property_angle_sum":
            # Check that the premise contains a valid Polygon fact.
            version = args[0]
            if version == "1":
                poly_match = re.search(r'Polygon\((\w+)\)', premise)
                if not poly_match:
                    return return_error(GeometricError(
                        tier=ErrorTier.TIER2_PREMISE_VIOLATION,
                        message="Missing or invalid Polygon() in premise for triangle_property_angle_sum"
                    ))
                triangle_points = poly_match.group(1)
                if len(triangle_points) != 3:
                    return return_error(GeometricError(
                        tier=ErrorTier.TIER2_PREMISE_VIOLATION,
                        message=f"Polygon({triangle_points}) does not represent a triangle (3 vertices expected)"
                    ))
                # Optionally, check that the triangle provided in the theorem call (e.g., args[1]) matches the Polygon.
                if len(args) >= 2 and args[1].strip() != triangle_points:
                    return return_error(GeometricError(
                        tier=ErrorTier.TIER2_PREMISE_VIOLATION,
                        message=f"Polygon in premise ({triangle_points}) does not match the triangle in theorem call ({args[1].strip()})"
                    ))
                # Premise is valid.
                return True, None
            else:
                return return_error(GeometricError(
                    tier=ErrorTier.TIER1_THEOREM_CALL_SYNTAX_VIOLATION,
                    message="these is no such version for the theorem",
                    details="these is no such version for the theorem triangle_property_angle_sum"
                ))






        elif theorem_name == "mirror_similar_triangle_judgment_aa":
            version = args[0]
            if version != "1":
                return return_error(GeometricError(
                    tier=ErrorTier.TIER1_THEOREM_CALL_SYNTAX_VIOLATION,
                    message="these is no such version for the theorem",
                    details="these is no such version for the theorem mirror_similar_triangle_judgment_aa"
                ))
            if len(args) < 3:
                return return_error(GeometricError(

                    tier=ErrorTier.TIER1_THEOREM_CALL_SYNTAX_VIOLATION,

                    message="Insufficient arguments for mirror_similar_triangle_judgment_aa",

                    details="Expected mirror_similar_triangle_judgment_aa(1, triangle1, triangle2)"

                ))

            triangle1 = args[1].strip()

            triangle2 = args[2].strip()

            if self.normalize_triangle(triangle1) not in self.polygons:
                return return_error(GeometricError(

                    tier=ErrorTier.TIER2_PREMISE_VIOLATION,

                    message=f"Polygon for triangle {triangle1} is missing",

                    details="The construction data did not define this polygon."

                ))

            if self.normalize_triangle(triangle2) not in self.polygons:
                return return_error(GeometricError(

                    tier=ErrorTier.TIER2_PREMISE_VIOLATION,

                    message=f"Polygon for triangle {triangle2} is missing",

                    details="The construction data did not define this polygon."

                ))

            # Check that the premise includes the required angle equalities.

            # For example, in the given premise:

            #   "Polygon(EGH)&Polygon(FEG)&Equal(MeasureOfAngle(EGH),MeasureOfAngle(EGF))&Equal(MeasureOfAngle(GHE),MeasureOfAngle(FEG))"

            # we want to check that the angle equalities hold.

            conjuncts = [p.strip() for p in premise.split('&')]

            for conj in conjuncts:

                if conj.startswith("Equal(MeasureOfAngle("):

                    m = re.match(r'Equal\(MeasureOfAngle\((\w{3})\),\s*MeasureOfAngle\((\w{3})\)\)', conj)

                    if m:

                        ang1 = m.group(1)

                        ang2 = m.group(2)

                        # Use your existing helper to check that these angles are forced equal.

                        if not self.check_angle_equality(ang1, ang2):
                            return return_error(GeometricError(

                                tier=ErrorTier.TIER2_PREMISE_VIOLATION,

                                message=f"Premise angle equality {ang1} = {ang2} does not hold.",

                                details="The constraints do not force these two angles to be equal."

                            ))

                    else:

                        return return_error(GeometricError(

                            tier=ErrorTier.TIER2_PREMISE_VIOLATION,

                            message=f"Angle equality clause '{conj}' is not in the expected format.",

                            details="Expected format: Equal(MeasureOfAngle(XXX),MeasureOfAngle(YYY))"

                        ))

            return True, None


        elif theorem_name == "mirror_similar_triangle_property_line_ratio":
            version = args[0]
            if version != "1":
                return return_error(GeometricError(
                    tier=ErrorTier.TIER1_THEOREM_CALL_SYNTAX_VIOLATION,
                    message="these is no such version for the theorem",
                    details="these is no such version for the theorem mirror_similar_triangle_property_line_ratio"
                ))
            similar_match = re.search(r'MirrorSimilarBetweenTriangle\((\w+),(\w+)\)', premise)
            if not similar_match:
                return return_error(GeometricError(
                    tier=ErrorTier.TIER2_PREMISE_VIOLATION,
                    message="Missing MirrorSimilarBetweenTriangle(...) in premise",
                    details="mirror_similar_triangle_property_line_ratio requires mirror similar triangles"
                ))
            tri1, tri2 = similar_match.groups()
            canonical_pair = self.canonicalize_mirror_triangle_pair(tri1, tri2)
            if canonical_pair not in self.mirror_similar_triangles:
                return return_error(GeometricError(
                    tier=ErrorTier.TIER2_PREMISE_VIOLATION,
                    message=f"Triangles {tri1} and {tri2} are not proven mirror similar",
                    details=f"Known mirror similar triangles: {self.mirror_similar_triangles}"
                ))
            return True, None




        elif theorem_name == "parallel_property_corresponding_angle":

            version = args[0]

            # Common check: the premise must include a ParallelBetweenLine fact.
            if version not in ["1","2"]:
                return_error(GeometricError(
                    tier=ErrorTier.TIER1_THEOREM_CALL_SYNTAX_VIOLATION,
                    message=f"no such version for the theorem",
                    details=f"no such version for the theorem parallel_property_corresponding_angle"
                ))
            if "ParallelBetweenLine" not in premise:
                return return_error(GeometricError(

                    tier=ErrorTier.TIER2_PREMISE_VIOLATION,

                    message="Missing parallel lines in premise",

                    details="parallel_property_corresponding_angle theorem requires ParallelBetweenLine(...)"

                ))

            line_match = re.search(r'ParallelBetweenLine\(\s*(\w+)\s*,\s*(\w+)\s*\)', premise)

            if not line_match:
                return return_error(GeometricError(

                    tier=ErrorTier.TIER2_PREMISE_VIOLATION,

                    message="Invalid parallel lines format in premise"

                ))

            line1, line2 = line_match.group(1), line_match.group(2)

            # Check that these lines are recorded as parallel

            possible_pairs = [

                (line1, line2),

                (line2, line1),

                (line1[::-1], line2),

                (line1, line2[::-1]),

                (line2[::-1], line1),

                (line2, line1[::-1])

            ]

            if not any((pair in self.parallel_pairs or pair[::-1] in self.parallel_pairs)

                       for pair in possible_pairs):
                return return_error(GeometricError(

                    tier=ErrorTier.TIER2_PREMISE_VIOLATION,

                    message=f"Lines {line1} and {line2} not proven parallel",

                    details=f"Available parallel pairs: {self.parallel_pairs}"

                ))

            # For version 2 we require an additional collinearity fact.

            if version == "2":

                # In our sample for version 2, the theorem call is parallel_property_corresponding_angle(2,HD,FB,A)

                # and the premise includes a Collinear fact—for instance, "Collinear(HFA)".

                token4 = args[3]  # e.g. "A"

                collinear_match = re.search(r'Collinear\(\s*(\w+)\s*\)', premise)

                if collinear_match:

                    points = collinear_match.group(1)

                    if token4 not in points:
                        return return_error(GeometricError(

                            tier=ErrorTier.TIER2_PREMISE_VIOLATION,

                            message=f"Premise for version 2 must include a Collinear fact containing '{token4}'",

                            details=f"Premise provided: {premise}"

                        ))

                else:

                    return return_error(GeometricError(

                        tier=ErrorTier.TIER2_PREMISE_VIOLATION,

                        message="Premise for version 2 must include a Collinear fact.",

                        details=f"Premise provided: {premise}"

                    ))

            return True, None





        elif theorem_name == "similar_triangle_property_line_ratio":

            version = args[0]

            if version == "1":

                similar_match = re.search(r'SimilarBetweenTriangle\((\w+),(\w+)\)', premise)

                if not similar_match:
                    # Add return here

                    return return_error(GeometricError(

                        tier=ErrorTier.TIER2_PREMISE_VIOLATION,

                        message="Missing similar triangles in premise",

                        details="similar_triangle_property_line_ratio requires similar triangles"

                    ))

                tri1, tri2 = similar_match.groups()

                if not self.are_triangles_similar(tri1, tri2):
                    # Add return here

                    return return_error(GeometricError(

                        tier=ErrorTier.TIER2_PREMISE_VIOLATION,

                        message=f"Triangles {tri1} and {tri2} are not proven similar",

                        details=f"Known similar triangles: {self.similar_triangles}"

                    ))

                # If all checks pass, return success

                return True, None

            else:
                return return_error(GeometricError(
                    tier=ErrorTier.TIER1_THEOREM_CALL_SYNTAX_VIOLATION,
                    message="these is no such version for the theorem",
                    details="these is no such version for the theorem similar_triangle_property_line_ratio"
                ))



        elif theorem_name == "parallelogram_property_opposite_angle_equal":

            version = args[0]
            if version == "1":
                if len(args) < 2:
                    return return_error(GeometricError(

                        tier=ErrorTier.TIER1_THEOREM_CALL_SYNTAX_VIOLATION,

                        message="Missing parallelogram argument",

                        details="parallelogram_property_opposite_angle_equal requires a parallelogram name"

                    ))

                theorem_para = args[1]

                premise_match = re.search(r'Parallelogram\((\w+)\)', premise)

                if not premise_match:
                    return return_error(GeometricError(

                        tier=ErrorTier.TIER2_PREMISE_VIOLATION,

                        message="Invalid parallelogram format in premise"

                    ))

                premise_para = premise_match.group(1)

                # Get all valid cyclic variations of both parallelograms

                theorem_variations = self.normalize_parallelogram(theorem_para)

                premise_variations = self.normalize_parallelogram(premise_para)

                # Check if there's any overlap between the variations

                if not (theorem_variations & premise_variations):
                    return return_error(GeometricError(

                        tier=ErrorTier.TIER2_PREMISE_VIOLATION,

                        message=f"Theorem uses parallelogram {theorem_para} but premise specifies {premise_para}",

                        details=f"No matching cyclic variation found between theorem and premise parallelograms"

                    ))

                # Also check if either parallelogram is defined in TEXT_CDL

                if not any(var in self.parallelograms for var in theorem_variations):
                    return return_error(GeometricError(

                        tier=ErrorTier.TIER2_PREMISE_VIOLATION,

                        message=f"Parallelogram {theorem_para} is not defined in TEXT_CDL",

                        details=f"Available parallelograms: {', '.join(self.parallelograms)}"

                    ))
                return True, None
            else:
                return return_error(GeometricError(

                    tier=ErrorTier.TIER1_THEOREM_CALL_SYNTAX_VIOLATION,

                    message="no such version",

                    details="no such version for parallelogram_property_opposite_angle_equal"

                ))





        elif theorem_name == "similar_triangle_judgment_aa":
            version = args[0]
            if version == "1":
                if len(args) < 3:
                    return return_error(GeometricError(
                        tier=ErrorTier.TIER1_THEOREM_CALL_SYNTAX_VIOLATION,
                        message="Insufficient arguments for similar_triangle_judgment_aa",
                        details="Expected similar_triangle_judgment_aa(1, triangle1, triangle2)"
                    ))
                triangle1 = args[1].strip()  # e.g. "ADC"
                triangle2 = args[2].strip()  # e.g. "AEB"

                # First, check that these polygons exist in our stored polygons.
                norm_triangle1 = self.normalize_triangle(triangle1)
                norm_triangle2 = self.normalize_triangle(triangle2)
                if norm_triangle1 not in self.polygons:
                    return return_error(GeometricError(
                        tier=ErrorTier.TIER2_PREMISE_VIOLATION,
                        message=f"Polygon for triangle {triangle1} is missing from the input data.",
                        details="The construction data did not define this polygon."
                    ))
                if norm_triangle2 not in self.polygons:
                    return return_error(GeometricError(
                        tier=ErrorTier.TIER2_PREMISE_VIOLATION,
                        message=f"Polygon for triangle {triangle2} is missing from the input data.",
                        details="The construction data did not define this polygon."
                    ))
                # Next, check that the premise includes a polygon fact for each triangle.
                poly_matches = re.findall(r'Polygon\((\w+)\)', premise)
                if not any(triangle1 == poly or set(triangle1) == set(poly) for poly in poly_matches):
                    return return_error(GeometricError(
                        tier=ErrorTier.TIER2_PREMISE_VIOLATION,
                        message=f"Polygon for triangle {triangle1} is missing in the premise",
                        details="similar_triangle_judgment_aa requires a Polygon fact for the triangle"
                    ))
                if not any(triangle2 == poly or set(triangle2) == set(poly) for poly in poly_matches):
                    return return_error(GeometricError(
                        tier=ErrorTier.TIER2_PREMISE_VIOLATION,
                        message=f"Polygon for triangle {triangle2} is missing in the premise",
                        details="similar_triangle_judgment_aa requires a Polygon fact for the triangle"
                    ))
                # Now check that all angle equalities in the premise hold.
                # (For example, the premise may be:
                #  "Polygon(ADC)&Polygon(AEB)&Equal(MeasureOfAngle(ADC),MeasureOfAngle(AEB))&
                #   Equal(MeasureOfAngle(DCA),MeasureOfAngle(EBA))"
                # )
                # We split on '&' and for every clause that begins with "Equal(MeasureOfAngle(" we check the equality.
                conjuncts = [p.strip() for p in premise.split('&')]
                for conj in conjuncts:
                    # If this conjunct is an angle equality, it should match the pattern:
                    # Equal(MeasureOfAngle(XXX),MeasureOfAngle(YYY))
                    if conj.startswith("Equal(MeasureOfAngle("):
                        m = re.match(r'Equal\(MeasureOfAngle\((\w{3})\),\s*MeasureOfAngle\((\w{3})\)\)', conj)
                        if m:
                            ang1 = m.group(1)
                            ang2 = m.group(2)
                            # Use the solver to check that these two angles are forced equal.
                            if not self.check_angle_equality(ang1, ang2):
                                return return_error(GeometricError(
                                    tier=ErrorTier.TIER2_PREMISE_VIOLATION,
                                    message=f"Premise angle equality {ang1} = {ang2} does not hold.",
                                    details="The constraints do not force these two angles to be equal."
                                ))
                        else:
                            # If the pattern does not match, you might choose to ignore or return an error.
                            return return_error(GeometricError(
                                tier=ErrorTier.TIER2_PREMISE_VIOLATION,
                                message=f"Angle equality clause '{conj}' is not in the expected format.",
                                details="Expected format: Equal(MeasureOfAngle(XXX),MeasureOfAngle(YYY))"
                            ))
                # If we got here, all parts of the premise are valid.
                return True, None
            else:
                return return_error(GeometricError(
                    tier=ErrorTier.TIER1_THEOREM_CALL_SYNTAX_VIOLATION,
                    message="these is no such version for the theorem",
                    details="these is no such version for the theorem similar_triangle_judgment_aa"
                ))






        elif theorem_name == "parallel_property_alternate_interior_angle":

            version = args[0]

            if version == "1":

                # Version 1: we require that a ParallelBetweenLine fact is present.

                if "ParallelBetweenLine" not in premise:
                    return return_error(GeometricError(

                        tier=ErrorTier.TIER2_PREMISE_VIOLATION,

                        message="Missing parallel lines in premise (version 1)",

                        details="parallel_property_alternate_interior_angle requires ParallelBetweenLine(...)"

                    ))

                line_match = re.search(r'ParallelBetweenLine\((\w+),\s*(\w+)\)', premise)

                if not line_match:
                    return return_error(GeometricError(

                        tier=ErrorTier.TIER2_PREMISE_VIOLATION,

                        message="Invalid parallel lines format in premise (version 1)"

                    ))

                # (Optionally, you can check that these lines are already recorded as parallel.)

                line1, line2 = line_match.group(1), line_match.group(2)

                possible_pairs = [

                    (line1, line2),

                    (line2, line1),

                    (line1[::-1], line2),

                    (line1, line2[::-1]),

                    (line2[::-1], line1),

                    (line2, line1[::-1])

                ]

                if not any(
                        (pair in self.parallel_pairs or pair[::-1] in self.parallel_pairs) for pair in possible_pairs):
                    return return_error(GeometricError(

                        tier=ErrorTier.TIER2_PREMISE_VIOLATION,

                        message=f"Lines {line1} and {line2} not proven parallel (version 1)",

                        details=f"Available parallel pairs: {self.parallel_pairs}"

                    ))

                # Premise is valid for version 1.

                return True, None

            elif version == "2":

                # Version 2: we require both a ParallelBetweenLine fact and an additional Line fact.

                if "ParallelBetweenLine" not in premise:
                    return return_error(GeometricError(

                        tier=ErrorTier.TIER2_PREMISE_VIOLATION,

                        message="Missing parallel lines in premise (version 2)",

                        details=f"Premise provided: {premise}"

                    ))

                if "Line(" not in premise:
                    return return_error(GeometricError(

                        tier=ErrorTier.TIER2_PREMISE_VIOLATION,

                        message="Missing Line fact in premise (version 2)",

                        details=f"Premise provided: {premise}"

                    ))

                # (Optionally, further checks can be added here.)

                return True, None
            else:
                return return_error(GeometricError(
                    tier=ErrorTier.TIER1_THEOREM_CALL_SYNTAX_VIOLATION,
                    message=f"no such version for the theorem",
                    details="no such version for the theorem parallel_property_alternate_interior_angle"
                ))


        elif theorem_name == "angle_addition":
            version = args[0]

            if version == "1":
                if len(args) < 3:
                    return return_error(GeometricError(
                        tier=ErrorTier.TIER1_THEOREM_CALL_SYNTAX_VIOLATION,
                        message="Missing angle arguments",
                        details="angle_addition requires at least two angles"
                    ))

                angle1 = args[1] if len(args) > 1 else ""
                angle2 = args[2] if len(args) > 2 else ""

                if len(angle1) != 3 or len(angle2) != 3:
                    return return_error(GeometricError(
                        tier=ErrorTier.TIER1_THEOREM_CALL_SYNTAX_VIOLATION,
                        message="Invalid angle format",
                        details="Each angle must be specified by exactly 3 points"
                    ))

                if angle1[1] != angle2[1]:
                    return return_error(GeometricError(
                        tier=ErrorTier.TIER2_PREMISE_VIOLATION,
                        message=f"Angles {angle1} and {angle2} must share a vertex",
                        details="Required for angle addition"
                    ))
                return True, None
            else:
                return return_error(GeometricError(
                    tier=ErrorTier.TIER1_THEOREM_CALL_SYNTAX_VIOLATION,
                    message=f"no such version for the theorem angle_addition",
                    details="no such version for the theorem angle_addition"
                ))


        elif theorem_name == "quadrilateral_property_angle_sum":
            version = args[0]
            if version != "1":
                return return_error(GeometricError(

                    tier=ErrorTier.TIER1_THEOREM_CALL_SYNTAX_VIOLATION,
                    message="these is no such version for the theorem",
                    details="these is no such version for the theorem for quadrilateral_property_angle_sum"

                ))
            if len(args) < 2:
                return return_error(GeometricError(

                    tier=ErrorTier.TIER1_THEOREM_CALL_SYNTAX_VIOLATION,

                    message="Missing quadrilateral name"

                ))

            quad_name = args[1].strip()

            if quad_name not in self.polygons:
                return return_error(GeometricError(

                    tier=ErrorTier.TIER2_PREMISE_VIOLATION,

                    message=f"Quadrilateral {quad_name} not defined",

                    details=f"Known polygons: {self.polygons}"

                ))

            return True, None

        else:
            # Theorem name did not match any implemented validation checks
            error_message = f"Theorem '{theorem_name}' premise validation is not implemented in the verifier."
            error_details = f"Theorem '{theorem_name}' is not recognized or its premise validation is not supported by the current verifier version."
            # Use return_error to set the flag and return correctly formatted error
            return return_error(GeometricError(
                tier=ErrorTier.TIER1_THEOREM_CALL_SYNTAX_VIOLATION,
                message=error_message,
                details=error_details
            ))

    def parse_and_verify_proof(self, content: str) -> bool:
        def check_gt_answer(model_answer_numeric, model_answer_symbolic):
            """Check if GT_ANSWER exists and matches the model answer"""
            if not model_response_content:
                return True, ""

            end_idx = content.find("***MODEL_RESPONSE_END***")
            if end_idx == -1:
                return True, ""

            post_model_content = content[end_idx + len("***MODEL_RESPONSE_END***"):]
            gt_match = re.search(r'GT_ANSWER:\s*([^\s\n]+)', post_model_content)
            if not gt_match:
                return True, ""

            try:
                gt_answer_str = gt_match.group(1).strip()
                gt_answer_numeric, gt_answer_symbolic = parse_special_answer(gt_answer_str)

                if abs(gt_answer_numeric - model_answer_numeric) > epsilon:
                    # Create a more specific feedback message with clear "MODEL vs GROUND TRUTH" format
                    detailed_feedback = "verification failed.\n\n"
                    detailed_feedback += f"- Goal: value determination\n"
                    detailed_feedback += f"- Model answer: {model_answer_symbolic}\n"
                    detailed_feedback += f"- Verifier expected answer: {gt_answer_str}\n"
                    detailed_feedback += f"- Error: THE MODEL DETERMINED THE ANSWER TO BE {model_answer_symbolic} BUT IN THE GROUND TRUTH SOLUTION TO THE PROBLEM THE ANSWER IS {gt_answer_str}.\n"
                    detailed_feedback += f"  Please review your theorem sequence and ensure it correctly establishes the expected answer.\n\n"
                    detailed_feedback += "Please fix the proof."

                    print(
                        f"Model answer {model_answer_symbolic} ({model_answer_numeric}) differs from GT answer {gt_answer_str} ({gt_answer_numeric})")
                    return False, detailed_feedback
                return True, ""
            except Exception as e:
                print(f"Error comparing with GT_ANSWER: {e}")
                return True, ""  # Continue with regular verification on error
        try:

            feedback = ""
            self.parallelograms = set()
            self.collinear_facts = []
            self.parallel_pairs = set()
            sections = {}
            current_section = None

            # Parse sections (keep existing section parsing code)
            print("\nParsing sections...")
            for line in content.split('\n'):
                line = line.strip()
                if not line:
                    continue

                # Modified section detection
                if (line.endswith('CDL:') or
                        line.endswith('CDL_EXTENDED:') or  # Added this line
                        line.endswith('SEQUENCE:') or
                        line == 'ANSWER:'):
                    current_section = line[:-1] if line.endswith(':') else line
                    sections[current_section] = []
                    print(f"Found section: {current_section}")
                elif current_section:
                    sections[current_section].append(line)

            print("\nAvailable sections:", list(sections.keys()))

            # Extract content between MODEL_RESPONSE_BEGIN and MODEL_RESPONSE_END if present
            model_response_content = None
            gt_answer = None
            if len(content) > 0:
                start_marker = "***MODEL_RESPONSE_BEGIN***"
                end_marker = "***MODEL_RESPONSE_END***"
                start_idx = content.find(start_marker)

                if start_idx != -1:
                    start_idx += len(start_marker)
                    end_idx = content.find(end_marker, start_idx)

                    if end_idx != -1:
                        model_response_content = content[start_idx:end_idx].strip()

                        # Parse sections within the model response content
                        model_sections = {}
                        current_model_section = None

                        for line in model_response_content.split('\n'):
                            line = line.strip()
                            if not line:
                                continue

                            # Match any string ending with "ANSWER:" including "RETRY_ANSWER:"
                            if line.endswith("ANSWER:") or "_ANSWER:" in line:
                                current_model_section = ANSWER
                                model_sections[current_model_section] = []
                            # Match any string ending with "THEOREM_SEQUENCE:" including "RETRY_THEOREM_SEQUENCE:"
                            elif line.endswith("THEOREM_SEQUENCE:")or "_THEOREM_SEQUENCE:" in line:
                                current_model_section = THEOREM_SEQUENCE
                                model_sections[current_model_section] = []
                            elif current_model_section and line.endswith(':'):
                                current_model_section = line[:-1]
                                model_sections[current_model_section] = []
                            elif current_model_section:
                                model_sections[current_model_section].append(line)

                        # Override the original sections with the model response sections
                        if ANSWER in model_sections:
                            sections[ANSWER] = model_sections[ANSWER]
                        if THEOREM_SEQUENCE in model_sections:
                            sections[THEOREM_SEQUENCE] = model_sections[THEOREM_SEQUENCE]
                    else:
                        # --- ADDED ELSE BLOCK for missing END marker ---
                        # Start marker found, but end marker was NOT found after it
                        error_message = f"Found '{start_marker}' but could not find the '{end_marker}' marker afterwards."
                        print(f"Error: {error_message}")
                        # Create a TIER1 error object (optional, but good practice)
                        error = GeometricError(
                            tier=ErrorTier.TIER1_THEOREM_CALL_SYNTAX_VIOLATION,
                            message=error_message,
                            details="The proof structure is incorrect. Ensure both markers exist and are in the correct order."
                        )
                        # Return False with the formatted TIER1 error message
                        # Prioritize details if available, otherwise use message
                        error_content = error.details if error.details else error.message
                        return False, f"Error in {error.tier.name}: {error_content}"
                        # --- END OF ADDED ELSE BLOCK ---
                else:
                    # --- ADDED ELSE BLOCK for missing START marker ---
                    # Start marker was NOT found
                    error_message = f"Could not find the '{start_marker}' marker."
                    print(f"Error: {error_message}")
                    # Create a TIER1 error object
                    error = GeometricError(
                        tier=ErrorTier.TIER1_THEOREM_CALL_SYNTAX_VIOLATION,
                        message=error_message,
                        details="The proof structure is incorrect. The required starting marker is missing."
                    )
                    # Return False with the formatted TIER1 error message
                    # Prioritize details if available, otherwise use message
                    error_content = error.details if error.details else error.message
                    return False, f"Error in {error.tier.name}: {error_content}"


            # adding all the points from the CONSTRUCTION_CDL_EXTENDED for the collinear
            if CONSTRUCTION_CDL_EXTENDED in sections:
                for line in sections[CONSTRUCTION_CDL_EXTENDED]:
                    if line.startswith('Point('):
                        name = line[6:-1]
                        self.add_point(name)

            if CONSTRUCTION_CDL in sections:
                print("\nProcessing CONSTRUCTION_CDL section...")
                for line in sections[CONSTRUCTION_CDL]:
                    print(f"Processing line: {line}")
                    if line.startswith('Collinear('):
                        points = line[10:-1]  # Extract points
                        normalized_points = self.normalize_collinear_points(points)
                        if normalized_points not in [''.join(fact) for fact in self.collinear_facts]:
                            self.collinear_facts.append(list(normalized_points))
                            self.add_collinear_fact(list(normalized_points))
                            print(f"Added normalized collinear points: {normalized_points}")
            # Process CONSTRUCTION_CDL_EXTENDED first

            if CONSTRUCTION_CDL_EXTENDED in sections:
                last_prefix = None
                current_type = None
                print("\nProcessing CONSTRUCTION_CDL_EXTENDED section...")
                for line in sections[CONSTRUCTION_CDL_EXTENDED]:
                    print(f"Processing line: {line}")
                    if line.startswith('Collinear('):
                        points = line[10:-1]  # Extract points from "Collinear(...)"

                        # If there are more than 3 points, break it down into all possible 3-point combinations
                        if len(points) > 3:
                            from itertools import combinations
                            for sub_points in combinations(points, 3):
                                three_points = ''.join(sub_points)
                                normalized_points = self.normalize_collinear_points(three_points)
                                normalized_str = ''.join(normalized_points)



                                # Otherwise, add it
                                self.collinear_facts.append(list(normalized_points))
                                self.add_collinear_fact(list(normalized_points))
                                print(f"Added normalized collinear points (extended): {normalized_points}")
                        else:
                            # Original behavior for 3 or fewer points
                            normalized_points = self.normalize_collinear_points(points)
                            normalized_str = ''.join(normalized_points)

                            # If the same fact appears in the main CONSTRUCTION_CDL section, skip it


                            # Otherwise, add it
                            self.collinear_facts.append(list(normalized_points))
                            self.add_collinear_fact(list(normalized_points))
                            print(f"Added normalized collinear points (extended): {normalized_points}")
                            # Handle lines starting with ".."
                            last_prefix = 'Collinear('
                    if line.startswith('..'):
                        print(f"Found dotted line, current_type is: {current_type}")  # Debug
                        if current_type is not None:
                            # Extract content inside the parentheses after ".."
                            match = re.search(r'\(\s*(.+?)\s*\)', line)
                            if match:
                                content = match.group(1)
                                print(f"Extracted content from dotted line: {content}")  # Debug

                                # Process based on current_type
                                if current_type == "Cocircular":
                                    # Process content as Cocircular data
                                    raw_fields = content.split(',')
                                    points = []
                                    for token in raw_fields:
                                        token = token.strip()
                                        # If token length > 1, expand into individual letters
                                        if len(token) > 1:
                                            points.extend(list(token))
                                        else:
                                            points.append(token)

                                    # Create canonical representation
                                    if points:
                                        fixed = points[0]
                                        others = sorted(points[1:])
                                        canonical = (fixed,) + tuple(others)
                                    else:
                                        canonical = tuple(points)

                                    self.cocircular_facts.append(canonical)
                                    print(f"Added cocircular fact from '..' line (canonical): {canonical}")
                                # Add other type handlers here
                            else:
                                print(f"Warning: Could not extract content from '..' line: {line}")
                        else:
                            print(f"Warning: Found '..' line without context: {line}")
                    if line.startswith('ParallelBetweenLine('):
                        match = re.search(r'ParallelBetweenLine\((\w+),\s*(\w+)\)', line)
                        if match:
                            line1, line2 = match.group(1), match.group(2)
                            print(f"Found parallel lines: {line1} || {line2}")
                            # Add all possible orientations
                            self.parallel_pairs.add((line1, line2))
                            self.parallel_pairs.add((line2, line1))
                            self.parallel_pairs.add((line1[::-1], line2))
                            self.parallel_pairs.add((line1, line2[::-1]))
                            print(f"Added parallel pairs: {line1} || {line2} and variations")
                            last_prefix = 'ParallelBetweenLine('
                    if line.startswith('Line('):
                        match = re.match(r'Line\((\w+)\)', line)
                        if match:
                            line_name = match.group(1)
                            if len(line_name) == 2:  # Ensure it's a two-point line
                                normalized_line = self.normalize_line_name(line_name)
                                self.defined_lines.add(normalized_line)
                                print(f"Added defined line: {normalized_line}")
                                last_prefix = 'Line('
                            else:
                                print(f"Warning: Skipping invalid Line format: {line}")
                    if line.startswith('Shape('):
                        continue
                        # Skip SYMBOLS_AND_VALUES, EQUATIONS
                    if line.startswith('SYMBOLS_AND_VALUES:') or line.startswith('EQUATIONS:'):
                        continue
                    if line.startswith('Parallelogram('):
                        match = re.match(r'Parallelogram\((\w+)\)', line)
                        if match:
                            para_name = match.group(1)
                            print(f"Found parallelogram in TEXT_CDL: {para_name}")
                            self.parallelograms.update(get_cyclic_variations(para_name))
                            print(f"Added parallelogram variations: {self.parallelograms}")
                            last_prefix = 'Parallelogram('
                            current_type = "Parallelogram"
                    elif line.startswith('PerpendicularBetweenLine('):

                        match = re.match(r'PerpendicularBetweenLine\((\w+),\s*(\w+)\)', line)

                        if match:
                            line1, line2 = match.group(1), match.group(2)

                            print(f"Found perpendicular lines: {line1} ⊥ {line2}")

                            # Add both orientations to perpendicular pairs

                            self.perpendicular_pairs.add((line1, line2))

                            self.perpendicular_pairs.add((line2, line1))

                            # Find the shared vertex (common point between lines)

                            vertex = next(p for p in line1 if p in line2)

                            # Get the non-shared points from each line

                            first_point = next(p for p in line2 if p != vertex)  # From second line

                            last_point = next(p for p in line1 if p != vertex)  # From first line

                            # Create and normalize the 90° angle name: for BC⊥AC we get ACB = 90°

                            angle = f"{first_point}{vertex}{last_point}"

                            normalized_angle = self.normalize_angle_name(angle)

                            # Add the angle to both Z3 solver and known values

                            angle_var = self.add_angle(first_point, vertex, last_point)

                            self.solver.add(angle_var == 90)

                            print(f"Added 90° perpendicular angle constraint: {normalized_angle}")
                            last_prefix = 'PerpendicularBetweenLine('
                    elif line.startswith("Arc("):
                        # Extract the arc name from e.g. "Arc(OBM)"
                        arc_name = line[4:-1].strip()
                        self.add_arc(arc_name)
                        last_prefix = 'Arc('
                    if line.startswith('Polygon('):
                        # Extract the polygon name; for instance, "ABC" from "Polygon(ABC)"
                        poly_match = re.match(r'Polygon\((\w+)\)', line)
                        if poly_match:
                            poly = poly_match.group(1)
                            # Normalize if you like (so that 'ABC' and 'BCA' are considered the same)
                            normalized_poly = self.normalize_triangle(poly) if len(poly) == 3 else poly
                            self.polygons.add(normalized_poly)
                            print(f"Added polygon: {normalized_poly}")
                            last_prefix = 'Polygon('
                    elif line.startswith("Circle("):
                        # e.g. "Circle(D)" means we have a circle named D
                        circle_name = line[7:-1]  # get whatever is inside Circle(...)
                        # create radius, diameter, area Real variables if not already present
                        if circle_name not in self.circle_radii:
                            self.circle_radii[circle_name] = Real(f"radius_{circle_name}")
                            self.solver.add(self.circle_radii[circle_name] >= 0)
                        if circle_name not in self.circle_diameters:
                            # We'll store the diameter as another Z3 variable if needed
                            # but typically we only store "diameterOfCircle(D)" if a theorem sets it equal
                            pass
                        if circle_name not in self.circle_areas:
                            self.circle_areas[circle_name] = Real(f"area_{circle_name}")
                            self.solver.add(self.circle_areas[circle_name] >= 0)
                        last_prefix = 'Circle('
                    elif line.startswith("Rhombus("):

                        match = re.match(r"Rhombus\((\w+)\)", line)

                        if match:
                            last_prefix = 'Rhombus('
                            shape_name = match.group(1)

                            self.rhombi.add(shape_name)

                            # Add side equality constraints for the rhombus

                            if len(shape_name) >= 4:  # Ensure we have at least 4 vertices

                                # Extract all adjacent vertex pairs (sides of the rhombus)

                                sides = []

                                for i in range(len(shape_name)):
                                    side = shape_name[i] + shape_name[(i + 1) % len(shape_name)]

                                    sides.append(side)

                                # Create length variables for all sides

                                side_vars = []

                                for side in sides:
                                    side_var = self.add_length(side[0], side[1])

                                    side_vars.append(side_var)

                                # Add constraints that all sides are equal to each other

                                for i in range(1, len(side_vars)):
                                    self.solver.add(side_vars[0] == side_vars[i])

                                print(f"Added rhombus side equality constraints for {shape_name}: {' = '.join(sides)}")
                    elif line.startswith('Cocircular('):
                        # Process normal Cocircular line
                        inside = line[11:-1]  # This will be "B,UVTS" from "Cocircular(B,UVTS)"
                        raw_fields = inside.split(',')
                        points = []
                        for token in raw_fields:
                            token = token.strip()
                            # If token length > 1, expand into individual letters
                            if len(token) > 1:
                                points.extend(list(token))
                            else:
                                points.append(token)

                        # Create canonical representation
                        if points:
                            fixed = points[0]
                            others = sorted(points[1:])
                            canonical = (fixed,) + tuple(others)
                        else:
                            canonical = tuple(points)

                        self.cocircular_facts.append(canonical)
                        print(f"Added cocircular fact (canonical): {canonical}")
                        # Update current_type for potential ".." lines that follow
                        current_type = "Cocircular"
                        print(f"Set current_type to: {current_type}")  # Debug
                    elif line.startswith("Kite("):
                        match = re.match(r"Kite\((\w+)\)", line)
                        if match:
                            shape_name = match.group(1)
                            self.kites.add(shape_name)

                    if line.startswith('Point('):
                        name = line[6:-1]
                        self.add_point(name)
                    elif line.startswith('ParallelBetweenLine('):
                        match = re.search(r'ParallelBetweenLine\((\w+),\s*(\w+)\)', line)
                        if match:
                            line1, line2 = match.group(1), match.group(2)
                            print(f"Found parallel lines: {line1} || {line2}")
                            pair = tuple(sorted([line1, line2]))
                            self.parallel_pairs.add(pair)
                            # Add reversed pair too
                            self.parallel_pairs.add(tuple([line2, line1]))
                            print(f"Added parallel pairs: {pair} and {(line2, line1)}")

            # Parse goal and verify

            # Process CONSTRUCTION_CDL facts


            # Parse TEXT_CDL facts
            # Inside parse_and_verify_proof method
            # Inside parse_and_verify_proof method
            # Inside parse_and_verify_proof, when processing TEXT_CDL section:
            # Inside parse_and_verify_proof, modify the TEXT_CDL section:
            self.text_cdl_lines = []
            if TEXT_CDL in sections:
                self.text_cdl_lines = sections[TEXT_CDL]
                from fractions import Fraction
                for line in sections[TEXT_CDL]:
                    if line.startswith('Equal(MeasureOfAngle('):
                        angle_equality_match = re.match(r'Equal\(MeasureOfAngle\((\w+)\),MeasureOfAngle\((\w+)\)\)',
                                                        line)

                        if angle_equality_match:
                            angle1, angle2 = angle_equality_match.group(1), angle_equality_match.group(2)
                            print(f"Found angle equality in TEXT_CDL: {angle1} = {angle2}")

                            # Get or create the Z3 variables for both angles
                            angle1_var = self.add_angle(angle1[0], angle1[1], angle1[2])
                            angle2_var = self.add_angle(angle2[0], angle2[1], angle2[2])

                            # Add constraint that they are equal
                            self.solver.add(angle1_var == angle2_var)
                            print(f"Added angle equality constraint: {angle1} = {angle2}")

                        else:
                            # If not an angle = angle pattern, try the original angle = value pattern
                            value_match = re.match(r'Equal\(MeasureOfAngle\((\w+)\),(.*?)\)', line)
                            if value_match:
                                angle_name, expression = value_match.group(1), value_match.group(2).strip()
                                print(f"Found angle expression in TEXT_CDL: {angle_name} = {expression}")
                                self.add_algebraic_angle(angle_name, expression)
                            # Add this block to parse equilateral triangles
                    elif line.startswith('EquilateralTriangle('):
                        equilateral_match = re.match(r'EquilateralTriangle\((\w+)\)', line)
                        if equilateral_match:
                            triangle = equilateral_match.group(1)
                            print(f"Found equilateral triangle in TEXT_CDL: {triangle}")

                            # Initialize equilateral_triangles if needed
                            if not hasattr(self, "equilateral_triangles"):
                                self.equilateral_triangles = set()

                            # Add all cyclic rotations to the set
                            for i in range(len(triangle)):
                                rotation = triangle[i:] + triangle[:i]
                                self.equilateral_triangles.add(rotation)

                            # Since equilateral triangles are also isosceles triangles,
                            # add them to isosceles triangles set if it exists
                            if hasattr(self, "isosceles_triangles"):
                                for i in range(len(triangle)):
                                    rotation = triangle[i:] + triangle[:i]
                                    self.isosceles_triangles.add(rotation)
                            else:
                                # Create the isosceles_triangles set if it doesn't exist
                                self.isosceles_triangles = set()
                                for i in range(len(triangle)):
                                    rotation = triangle[i:] + triangle[:i]
                                    self.isosceles_triangles.add(rotation)

                            # Add constraint that all sides are equal
                            side1 = self.add_length(triangle[0], triangle[1])
                            side2 = self.add_length(triangle[1], triangle[2])
                            side3 = self.add_length(triangle[2], triangle[0])

                            self.solver.add(side1 == side2)
                            self.solver.add(side2 == side3)

                            # Add constraint that all angles equal 60°
                            angle1 = self.add_angle(triangle[0], triangle[1], triangle[2])
                            angle2 = self.add_angle(triangle[1], triangle[2], triangle[0])
                            angle3 = self.add_angle(triangle[2], triangle[0], triangle[1])

                            self.solver.add(angle1 == 60)
                            self.solver.add(angle2 == 60)
                            self.solver.add(angle3 == 60)

                            print(
                                f"Added equilateral triangle: {triangle} with all sides equal and all angles = 60°")
                    elif line.startswith('IsoscelesTriangle('):
                        match = re.match(r'IsoscelesTriangle\((\w+)\)', line)
                        if match:
                            triangle = match.group(1)
                            print(f"Found isosceles triangle in TEXT_CDL: {triangle}")

                            # Initialize isosceles_triangles if needed
                            if not hasattr(self, 'isosceles_triangles'):
                                self.isosceles_triangles = set()

                            # Add all rotations to handle different triangle representations
                            for i in range(len(triangle)):
                                rotation = triangle[i:] + triangle[:i]
                                self.isosceles_triangles.add(rotation)

                            # For a triangle ABC, assuming the pattern is:
                            # - Equal angles at B and C (second and third vertices)
                            # - Equal sides AB and AC (connecting first vertex to others)

                            # Add angle equality constraint
                            # For LNK, this would be angles LNK and NKL
                            angle1 = self.add_angle(triangle[0], triangle[1], triangle[2])  # LNK
                            angle2 = self.add_angle(triangle[1], triangle[2], triangle[0])  # NKL
                            self.solver.add(angle1 == angle2)
                            print(
                                f"Added isosceles triangle angle constraint: ∠{triangle[0]}{triangle[1]}{triangle[2]} = ∠{triangle[1]}{triangle[2]}{triangle[0]}")

                            # Add side equality constraint
                            # For LNK, this would be sides LN and LK
                            side1 = self.add_length(triangle[0], triangle[1])  # LN
                            side2 = self.add_length(triangle[0], triangle[2])  # LK
                            self.solver.add(side1 == side2)
                            print(
                                f"Added isosceles triangle side constraint: {triangle[0]}{triangle[1]} = {triangle[0]}{triangle[2]}")

                            # Store the theorem conclusion that would be generated
                            conclusion = f"Equal(MeasureOfAngle({triangle[0]}{triangle[1]}{triangle[2]}),MeasureOfAngle({triangle[1]}{triangle[2]}{triangle[0]}))"
                            if not hasattr(self, 'isosceles_conclusions'):
                                self.isosceles_conclusions = {}
                            self.isosceles_conclusions[triangle] = [conclusion]
                            print(f"Stored isosceles triangle conclusion: {conclusion}")
                        else:
                            print(f"Warning: Could not parse IsoscelesTriangle line: {line}")
                    elif line.startswith('MirrorCongruentBetweenTriangle('):
                        match = re.match(r'MirrorCongruentBetweenTriangle\((\w+),(\w+)\)', line)
                        if match:
                            tri1, tri2 = match.groups()
                            print(f"Found mirror congruent triangles in TEXT_CDL: {tri1} and {tri2}")
                            # Use the canonicalization function you provided
                            canonical_pair = self.canonicalize_mirror_congruent_triangle_pair(tri1, tri2)
                            # Store if not already present
                            if canonical_pair not in self.mirror_congruent_triangles:
                                self.mirror_congruent_triangles.append(canonical_pair)
                                print(
                                    f"Added mirror congruent triangles: {tri1} and {tri2} (canonical: {canonical_pair})")
                        else:
                            print(f"Warning: Could not parse MirrorCongruentBetweenTriangle line: {line}")
                    elif line.startswith('Equal(RadiusOfCircle('):
                        match = re.match(r'Equal\(RadiusOfCircle\((\w+)\),(.*?)\)', line)
                        if match:
                            circle_name, expression = match.groups()
                            expression = expression.strip()
                            print(f"Found radius value in TEXT_CDL: RadiusOfCircle({circle_name}) = {expression}")
                            try:
                                # Try parsing as numeric first
                                # Use Fraction for potentially better precision if input is like "1/5"
                                from fractions import Fraction
                                try:
                                    # Try Fraction first
                                    value = float(Fraction(expression))
                                except ValueError:
                                    # Fallback to direct float conversion
                                    value = float(expression)

                                # Get or create the radius variable
                                if circle_name not in self.circle_radii:
                                    self.circle_radii[circle_name] = Real(f"radius_{circle_name}")
                                    # Ensure radius is positive (or non-negative)
                                    self.solver.add(
                                        self.circle_radii[circle_name] > 0)  # Use > 0 for physical plausibility
                                radius_var = self.circle_radii[circle_name]

                                # Add the constraint
                                self.solver.add(radius_var == value)
                                print(f"Added numeric radius constraint: radius_{circle_name} = {value}")
                            except ValueError:
                                # Handle algebraic expression if necessary (less common for radius)
                                print(f"Warning: Could not parse radius value as numeric: {expression}")
                                variables = self.extract_variables(expression)
                                for var in variables:
                                    if var not in self.variables:
                                        self.variables[var] = Real(var)
                                        print(f"Created new variable for algebraic radius: {var}")
                                expr = self.parse_algebraic_expression(expression)
                                if circle_name not in self.circle_radii:
                                    self.circle_radii[circle_name] = Real(f"radius_{circle_name}")
                                    self.solver.add(self.circle_radii[circle_name] > 0)
                                radius_var = self.circle_radii[circle_name]
                                self.solver.add(radius_var == expr)
                                print(f"Added algebraic radius constraint: radius_{circle_name} = {expr}")
                    elif line.startswith('IsMidsegmentOfQuadrilateral('):
                        match = re.match(r'IsMidsegmentOfQuadrilateral\((\w+),(\w+)\)', line)
                        if match:
                            segment, quad = match.groups()

                            # Normalize quadrilateral name
                            norm_quad = self.normalize_quadrilateral(quad)

                            # Store both orientations of the segment
                            self.midsegments_of_quadrilaterals[(segment, norm_quad)] = True
                            self.midsegments_of_quadrilaterals[(segment[::-1], norm_quad)] = True

                            print(f"Recorded midsegment of quadrilateral: {segment} is a midsegment of {quad}")
                    elif line.startswith('Equal(LengthOfLine('):
                        # Try first to match length equality between two lines
                        equality_match = re.match(r'Equal\(LengthOfLine\((\w+)\),LengthOfLine\((\w+)\)\)', line)
                        if equality_match:
                            line1, line2 = equality_match.groups()
                            print(f"Found length equality in TEXT_CDL: {line1} = {line2}")
                            # Get variables for both lines
                            len1 = self.add_length(line1[0], line1[1])
                            len2 = self.add_length(line2[0], line2[1])
                            # Add equality constraint
                            self.solver.add(len1 == len2)
                            print(f"Added length equality constraint: {line1} = {line2}")
                            continue

                        # If not equality between lines, try the existing case for numeric/algebraic values
                        match = re.match(r'Equal\(LengthOfLine\((\w+)\),(.+)\)', line)
                        if match:
                            line_name, expression = match.groups()
                            expression = expression.strip()
                            print(f"Found length expression in TEXT_CDL: {line_name} = {expression}")
                            # Get (or create) the length variable
                            length_var = self.add_length(line_name[0], line_name[1])

                            try:
                                # Try parsing as numeric value first with math functions
                                import math
                                # Create a safe evaluation environment with only math functions
                                eval_env = {"sqrt": math.sqrt, "pi": math.pi}
                                value = float(eval(expression, {"__builtins__": {}}, eval_env))
                                self.solver.add(length_var == value)
                                print(f"Added numeric length constraint: {line_name} = {value}")
                            except Exception as e:
                                print(f"Could not evaluate as numeric: {expression}. Error: {e}")
                                # Handle as algebraic expression
                                variables = self.extract_variables(expression)
                                for var in variables:
                                    if var not in self.variables:
                                        self.variables[var] = Real(var)
                                        print(f"Created new variable for algebraic length: {var}")
                                expr = self.parse_algebraic_expression(expression)
                                self.solver.add(length_var == expr)
                                print(f"Added algebraic length constraint: {line_name} = {expr}")
                    elif line.startswith('MirrorSimilarBetweenTriangle('):
                        match = re.match(r'MirrorSimilarBetweenTriangle\((\w+),(\w+)\)', line)
                        if match:
                            tri1, tri2 = match.groups()
                            # You can reuse your existing canonicalization function
                            canonical_pair = self.canonicalize_mirror_triangle_pair(tri1, tri2)

                            if canonical_pair not in self.mirror_similar_triangles:
                                self.mirror_similar_triangles.append(canonical_pair)
                                print(
                                    f"Added mirror similar triangles: {tri1} and {tri2} (canonical: {canonical_pair})")
                    elif line.startswith('CongruentBetweenTriangle('):

                        match = re.match(r'CongruentBetweenTriangle\((\w+),(\w+)\)', line)

                        if match:

                            tri1, tri2 = match.groups()

                            canonical_pair = self.canonicalize_congruent_triangle_pair(tri1, tri2)

                            if not hasattr(self, "congruent_triangles"):
                                self.congruent_triangles = []

                            if canonical_pair not in self.congruent_triangles:
                                self.congruent_triangles.append(canonical_pair)

                            print(f"Added congruent triangles: {tri1} and {tri2} (canonical: {canonical_pair})")
                    elif line.startswith('Equal(PerimeterOfTriangle('):
                        # Match pattern like: Equal(PerimeterOfTriangle(OCD),23)
                        perimeter_match = re.match(r'Equal\(PerimeterOfTriangle\((\w+)\),(.+)\)', line)
                        if perimeter_match:
                            triangle_name, perimeter_value = perimeter_match.groups()
                            perimeter_value = perimeter_value.strip()
                            print(
                                f"Found triangle perimeter in TEXT_CDL: PerimeterOfTriangle({triangle_name}) = {perimeter_value}")

                            # Initialize triangle_perimeters if it doesn't exist
                            if not hasattr(self, 'triangle_perimeters'):
                                self.triangle_perimeters = {}

                            # Create perimeter variable if not already created
                            if triangle_name not in self.triangle_perimeters:
                                perimeter_var = Real(f"perimeter_{triangle_name}")
                                self.triangle_perimeters[triangle_name] = perimeter_var
                            else:
                                perimeter_var = self.triangle_perimeters[triangle_name]

                            # Parse perimeter value and add constraint
                            try:
                                # Try parsing as numeric value
                                import math
                                eval_env = {"sqrt": math.sqrt, "pi": math.pi}
                                value = float(eval(perimeter_value, {"__builtins__": {}}, eval_env))
                                self.solver.add(perimeter_var == value)
                                print(
                                    f"Added numeric perimeter constraint: PerimeterOfTriangle({triangle_name}) = {value}")

                                # Define perimeter as sum of sides
                                # For triangle ABC, sides are AB, BC, and CA
                                if len(triangle_name) == 3:
                                    # Create length variables for each side
                                    side1_var = self.add_length(triangle_name[0], triangle_name[1])
                                    side2_var = self.add_length(triangle_name[1], triangle_name[2])
                                    side3_var = self.add_length(triangle_name[2], triangle_name[0])

                                    # Define perimeter as sum of sides
                                    self.solver.add(perimeter_var == side1_var + side2_var + side3_var)
                                    print(f"Added perimeter definition: PerimeterOfTriangle({triangle_name}) = "
                                          f"LengthOfLine({triangle_name[0]}{triangle_name[1]}) + "
                                          f"LengthOfLine({triangle_name[1]}{triangle_name[2]}) + "
                                          f"LengthOfLine({triangle_name[2]}{triangle_name[0]})")
                            except Exception as e:
                                print(f"Could not evaluate as numeric: {perimeter_value}. Error: {e}")
                                # Handle algebraic expression if needed
                                variables = self.extract_variables(perimeter_value)
                                for var in variables:
                                    if var not in self.variables:
                                        self.variables[var] = Real(var)
                                        print(f"Created new variable for algebraic perimeter: {var}")
                                expr = self.parse_algebraic_expression(perimeter_value)
                                self.solver.add(perimeter_var == expr)
                                print(
                                    f"Added algebraic perimeter constraint: PerimeterOfTriangle({triangle_name}) = {expr}")
                    elif line.startswith('IsBisectorOfAngle('):
                        match = re.match(r'IsBisectorOfAngle\((\w+),(\w+)\)', line)
                        if match:
                            bisector_line, angle = match.groups()
                            print(f"Found angle bisector in TEXT_CDL: {bisector_line} bisects {angle}")

                            # Extract the three vertices of the angle
                            if len(angle) != 3:
                                print(f"Warning: Expected angle to have 3 vertices, but got {angle}")
                                continue

                            # Angle is specified as XYZ where Y is the vertex
                            # Bisector is specified as YO where Y is the vertex and O is some point
                            vertex = angle[1]

                            # Check if the bisector includes the vertex
                            if bisector_line[0] != vertex and bisector_line[1] != vertex:
                                print(f"Warning: Bisector {bisector_line} doesn't appear to include vertex {vertex}")
                                continue

                            # Extract the bisector point (not the vertex)
                            bisector_point = bisector_line[1] if bisector_line[0] == vertex else bisector_line[0]

                            # Form the two angles that should be equal
                            # If the angle is ABC and the bisector is BO, then ABO = CBO
                            first_point = angle[0]
                            third_point = angle[2]

                            angle1 = f"{first_point}{vertex}{bisector_point}"
                            angle2 = f"{third_point}{vertex}{bisector_point}"

                            # Normalize angle names
                            norm_angle1 = self.normalize_angle_name(angle1)
                            norm_angle2 = self.normalize_angle_name(angle2)

                            # Get or create the Z3 variables for both angles
                            angle1_var = self.add_angle(norm_angle1[0], norm_angle1[1], norm_angle1[2])
                            angle2_var = self.add_angle(norm_angle2[0], norm_angle2[1], norm_angle2[2])

                            # Add constraint that they are equal
                            self.solver.add(angle1_var == angle2_var)
                            print(f"Added angle bisector constraint: {norm_angle1} = {norm_angle2}")

                            # Store the bisector fact for later reference if needed
                            if not hasattr(self, 'angle_bisectors'):
                                self.angle_bisectors = []
                            self.angle_bisectors.append((bisector_line, angle))
                    elif line.startswith('IsAltitudeOfTriangle('):
                        match = re.match(r'IsAltitudeOfTriangle\((\w+),(\w+)\)', line)
                        if match:
                            altitude_line, triangle = match.groups()
                            print(
                                f"Found triangle altitude in TEXT_CDL: {altitude_line} is altitude of triangle {triangle}")

                            if len(triangle) != 3 or len(altitude_line) != 2:
                                print(f"Warning: Invalid format for altitude/triangle: {altitude_line}, {triangle}")
                                continue

                            vertex = None
                            for v_idx in range(len(triangle)):
                                if triangle[v_idx] == altitude_line[0]:  # Assume altitude starts at a vertex
                                    vertex = altitude_line[0]
                                    break
                                elif triangle[v_idx] == altitude_line[1]:  # Check other end too
                                    vertex = altitude_line[1]
                                    # Swap if vertex is second char in altitude_line
                                    altitude_line = altitude_line[::-1]
                                    break

                            if vertex is None:
                                print(
                                    f"Warning: Altitude line '{altitude_line}' doesn't start/end at a vertex of triangle '{triangle}'.")
                                continue

                            foot = altitude_line[1]  # The point where altitude meets the base (or its extension)
                            opposite_vertices = [v for v in triangle if v != vertex]

                            if len(opposite_vertices) != 2:
                                print(
                                    f"Warning: Could not identify opposite side for altitude {altitude_line} in {triangle}")
                                continue

                            # Add the 90-degree constraint.
                            # The angle is formed by one of the opposite vertices, the foot, and the vertex.
                            # Example: Altitude CD for triangle CAB. Vertex C, Foot D. Opposite A, B. Angle CDA = 90 or CDB = 90.
                            # Need collinearity (like ADB) to know which one. If D is *on* AB.
                            # Let's assume the standard case where the foot is on the opposite side segment.
                            # The angle is vertex-foot-opposite_vertex. e.g., CDB
                            angle_at_foot1 = self.add_angle(vertex, foot, opposite_vertices[0])
                            angle_at_foot2 = self.add_angle(vertex, foot, opposite_vertices[1])

                            # We need to determine which angle should be 90. Check collinearity.
                            base_collinear = None
                            foot_on_base_segment = False
                            for fact in self.collinear_facts:
                                fact_set = set(fact)
                                # Check if foot and opposite vertices are collinear
                                if foot in fact_set and set(opposite_vertices).issubset(fact_set):
                                    base_collinear = fact
                                    # Check if foot is BETWEEN the opposite vertices
                                    try:
                                        idx_f = fact.index(foot)
                                        idx_o1 = fact.index(opposite_vertices[0])
                                        idx_o2 = fact.index(opposite_vertices[1])
                                        if (idx_o1 < idx_f < idx_o2) or (idx_o2 < idx_f < idx_o1):
                                            foot_on_base_segment = True
                                    except ValueError:
                                        pass  # Point not found
                                    break

                            if foot_on_base_segment:
                                # If foot is between base vertices (e.g., ADB), both angles are 90
                                self.solver.add(angle_at_foot1 == 90)
                                self.solver.add(angle_at_foot2 == 90)
                                print(
                                    f"Added altitude constraints: ∠{vertex}{foot}{opposite_vertices[0]} = 90°, ∠{vertex}{foot}{opposite_vertices[1]} = 90°")
                            elif base_collinear:
                                # Foot is on the line extension. Assume one angle is 90. Which one?
                                # Convention needed. Let's assume the one involving the first opposite vertex?
                                self.solver.add(angle_at_foot1 == 90)
                                print(
                                    f"Added altitude constraint (foot on extension): ∠{vertex}{foot}{opposite_vertices[0]} = 90°")
                                # Could also infer the other is 180-90=90 if collinearity allows.
                                # self.solver.add(angle_at_foot2 == 90) # Might be redundant or incorrect depending on setup
                            else:
                                print(
                                    f"Warning: Collinearity of foot '{foot}' with base '{''.join(opposite_vertices)}' not established for altitude '{altitude_line}'. Cannot reliably set 90° angle.")

                            # Store the altitude fact if needed
                            if not hasattr(self, 'triangle_altitudes'): self.triangle_altitudes = []
                            self.triangle_altitudes.append((altitude_line, triangle))
                            if not hasattr(self, 'triangle_heights'):
                                self.triangle_heights = {}

                            # Get the length of the altitude line
                            altitude_length_var = self.add_length(altitude_line[0], altitude_line[1])

                            # Store this length as the height of the triangle
                            self.triangle_heights[triangle] = altitude_length_var
                            print(f"Connected altitude {altitude_line} as the height of triangle {triangle}")

                            # Also store for possible permutations of the triangle name
                            normalized_triangle = self.normalize_triangle(triangle)
                            for i in range(3):
                                variant = normalized_triangle[i:] + normalized_triangle[:i]
                                if variant != triangle:
                                    self.triangle_heights[variant] = altitude_length_var
                                    print(f"Also connected height to triangle variant {variant}")
                    elif line.startswith("IsPerpendicularBisectorOfLine("):
                        # Match a statement like: IsPerpendicularBisectorOfLine(EF,AC)
                        match = re.match(r'IsPerpendicularBisectorOfLine\((\w+),(\w+)\)', line)
                        if match:
                            bisector, bisected = match.groups()  # e.g., "EF", "AC"
                            print(f"Found perpendicular bisector: {bisector} is perpendicular bisector of {bisected}")

                            # Initialize perpendicular_bisectors attribute if it doesn't exist
                            if not hasattr(self, "perpendicular_bisectors"):
                                self.perpendicular_bisectors = set()
                            bisector_variations = [bisector, bisector[::-1]]

                            # For bisected AC, add (EF,AC), (EF,CA)
                            bisected_variations = [bisected, bisected[::-1]]

                            # Add all combinations
                            for b1 in bisector_variations:
                                for b2 in bisected_variations:
                                    self.perpendicular_bisectors.add((b1, b2))

                            print(f"Added perpendicular bisector relationships: {self.perpendicular_bisectors}")
                            # Find the intersection point (e.g., point on both bisector and bisected)
                            bisector_point = None  # This will be the intersection point

                            # Check all collinear facts to find where the lines meet
                            for fact in self.collinear_facts:
                                fact_str = ''.join(fact)
                                # Look for a point that's in both the bisector and a collinear fact with the bisected line
                                for point in bisector:
                                    if point in fact_str and all(p in fact_str for p in bisected):
                                        bisector_point = point
                                        break
                                if bisector_point:
                                    break

                            if not bisector_point:
                                # Try to infer the intersection point - look for a common point in both bisector and bisected
                                common_points = set(bisector).intersection(set(bisected))
                                if common_points:
                                    bisector_point = list(common_points)[0]
                                    print(f"Inferred intersection point: {bisector_point}")
                                else:
                                    print(
                                        f"Warning: Could not find the intersection point for perpendicular bisector {bisector} of {bisected}")
                                    continue  # Skip this statement

                            # Get the two parts of the bisected line
                            parts = [p for p in bisected]

                            # Add equal distance constraints for the two parts
                            # If bisected is AC and bisector_point is E, this adds AE = EC
                            dist1 = self.add_length(bisector_point, parts[0])
                            dist2 = self.add_length(bisector_point, parts[1])
                            self.solver.add(dist1 == dist2)
                            print(
                                f"Added equal distance constraint: {bisector_point}{parts[0]} = {bisector_point}{parts[1]}")

                            # Add right angle constraints
                            # If bisector is EF, get the other point (F)
                            other_point = next(p for p in bisector if p != bisector_point)

                            # Get collinear points for the intersection point
                            collinear_points = None
                            for fact in self.collinear_facts:
                                if bisector_point in fact:
                                    collinear_points = fact
                                    break

                            if collinear_points:
                                # Add right angle for points on the collinear line
                                for p in collinear_points:
                                    if p != bisector_point and p in bisected:  # Only for the endpoints of the bisected line
                                        angle = self.add_angle(other_point, bisector_point, p)  # e.g., FEA and FEC
                                        self.solver.add(angle == 90)
                                        print(f"Added 90° angle constraint for ∠{other_point}{bisector_point}{p}")
                            else:
                                # If no collinearity fact exists, still add right angles for the bisected endpoints
                                for p in parts:
                                    angle = self.add_angle(other_point, bisector_point, p)  # e.g., FEA and FEC
                                    self.solver.add(angle == 90)
                                    print(f"Added 90° angle constraint for ∠{other_point}{bisector_point}{p}")

                            # Also add collinearity for the three key points if not already present
                            bisected_with_bisector_point = parts[0] + bisector_point + parts[1]
                            normalized_collinear = self.normalize_collinear_points(bisected_with_bisector_point)

                            # Check if this collinearity is already recorded
                            collinear_exists = False
                            for fact in self.collinear_facts:
                                fact_str = self.normalize_collinear_points(''.join(fact))
                                if normalized_collinear == fact_str:
                                    collinear_exists = True
                                    break

                            if not collinear_exists:
                                # Add new collinearity fact
                                self.collinear_facts.append(list(normalized_collinear))
                                self.add_collinear_fact(list(normalized_collinear))
                                print(f"Added collinearity fact for {normalized_collinear}")

                            print(
                                f"Processed perpendicular bisector: {bisector_point} divides {bisected} equally with right angles")
                    elif line.startswith("Equal(AreaOfTriangle("):

                        # Parse text like: Equal(AreaOfTriangle(ABC),65) or Equal(AreaOfTriangle(ABC),Add(AreaOfTriangle(DCA),AreaOfTriangle(DAB)))

                        full_match = re.match(r'Equal\(AreaOfTriangle\((\w+)\),(.*)\)', line)

                        if full_match:

                            triangle, expression = full_match.groups()

                            expression = expression.strip()

                            # Normalize the primary triangle name

                            normalized_triangle = ''.join(sorted(triangle))

                            print(f"Found triangle area: AreaOfTriangle({triangle}) = {expression}")

                            # Create or get the primary triangle area variable

                            if normalized_triangle not in self.triangle_areas:
                                self.triangle_areas[normalized_triangle] = Real(f"areaTriangle_{normalized_triangle}")

                                self.solver.add(self.triangle_areas[normalized_triangle] >= 0)

                                print(f"Created triangle area variable: areaTriangle_{normalized_triangle}")

                            area_var = self.triangle_areas[normalized_triangle]

                            # Parse the right side based on its format

                            if expression.startswith("Add(AreaOfTriangle("):

                                # Debug output

                                print(f"Detected triangle addition expression: {expression}")

                                # Special case for Add(AreaOfTriangle(...),AreaOfTriangle(...))

                                # Find both triangles in the addition formula

                                triangle_pattern = r'AreaOfTriangle\((\w+)\)'

                                add_triangles = re.findall(triangle_pattern, expression)

                                # Debug output

                                print(f"Found triangles in addition: {add_triangles}")

                                if len(add_triangles) >= 2:

                                    # We have at least two triangles in the addition

                                    tri1, tri2 = add_triangles  # First two triangles

                                    # Normalize triangle names

                                    norm_tri1 = ''.join(sorted(tri1))

                                    norm_tri2 = ''.join(sorted(tri2))

                                    # Create variables for the summed triangles

                                    if norm_tri1 not in self.triangle_areas:
                                        self.triangle_areas[norm_tri1] = Real(f"areaTriangle_{norm_tri1}")

                                        self.solver.add(self.triangle_areas[norm_tri1] >= 0)

                                        print(f"Created triangle area variable: areaTriangle_{norm_tri1}")

                                    if norm_tri2 not in self.triangle_areas:
                                        self.triangle_areas[norm_tri2] = Real(f"areaTriangle_{norm_tri2}")

                                        self.solver.add(self.triangle_areas[norm_tri2] >= 0)

                                        print(f"Created triangle area variable: areaTriangle_{norm_tri2}")

                                    # Set up the addition constraint

                                    tri1_var = self.triangle_areas[norm_tri1]

                                    tri2_var = self.triangle_areas[norm_tri2]

                                    self.solver.add(area_var == tri1_var + tri2_var)

                                    print(f"Added constraint: Area({triangle}) = Area({tri1}) + Area({tri2})")

                                    print(f"Current triangle areas: {list(self.triangle_areas.keys())}")

                                else:

                                    print(f"WARNING: Could not extract triangles from addition: {expression}")

                            else:

                                # Handle numeric or algebraic expression as before

                                try:

                                    import math

                                    eval_env = {"sqrt": math.sqrt, "pi": math.pi}

                                    value = float(eval(expression, {"__builtins__": {}}, eval_env))

                                    self.solver.add(area_var == value)

                                    print(f"Added numeric triangle area constraint: Area({triangle}) = {value}")

                                except Exception as e:

                                    print(f"Could not evaluate as numeric: {expression}. Error: {e}")

                                    # Handle as algebraic expression

                                    variables = self.extract_variables(expression)

                                    for var in variables:

                                        if var not in self.variables:
                                            self.variables[var] = Real(var)

                                            print(f"Created new variable for algebraic area: {var}")

                                    expr = self.parse_algebraic_expression(expression)

                                    self.solver.add(area_var == expr)

                                    print(f"Added algebraic triangle area constraint: Area({triangle}) = {expr}")
                    elif line.startswith("IsMidpointOfLine("):
                        # Matches a fact like: IsMidpointOfLine(C,AO)
                        match = re.match(r'IsMidpointOfLine\((\w+),(\w+)\)', line)
                        if match:
                            midpoint, segment = match.groups()

                            # Make sure segment is a 2-character string representing the endpoints
                            if len(segment) != 2:
                                print(f"Error: Invalid segment format in IsMidpointOfLine({midpoint},{segment})")
                                continue

                            # Initialize midpoint tracking if not already present
                            if not hasattr(self, "midpoints"):
                                self.midpoints = {}

                            # Record the midpoint relationship
                            self.midpoints[(segment[0], segment[1])] = midpoint
                            # Also record the reverse order
                            self.midpoints[(segment[1], segment[0])] = midpoint

                            # Add the midpoint constraints to the solver:
                            # 1. The distance from first endpoint to midpoint equals distance from midpoint to second endpoint
                            # 2. The midpoint is on the line between the endpoints

                            # Get length variables for both half-segments
                            len1 = self.add_length(segment[0], midpoint)
                            len2 = self.add_length(midpoint, segment[1])

                            # Add equality constraint: AC = CB
                            self.solver.add(len1 == len2)

                            # Also add collinearity constraint if we track that explicitly
                            if not any(set([segment[0], midpoint, segment[1]]).issubset(set(''.join(fact))) for fact in
                                       self.collinear_facts):
                                collinear_points = [segment[0], midpoint, segment[1]]
                                normalized_points = self.normalize_collinear_points(''.join(collinear_points))
                                self.collinear_facts.append(list(normalized_points))
                                self.add_collinear_fact(list(normalized_points))
                                print(
                                    f"Added collinearity constraint for midpoint: {segment[0]}, {midpoint}, {segment[1]}")

                            print(f"Recorded midpoint: {midpoint} is the midpoint of segment {segment[0]}{segment[1]}")
                        else:
                            print("Error parsing IsMidpointOfLine fact in TEXT_CDL.")
                    elif line.startswith('ParallelBetweenLine('):

                        match = re.search(r'ParallelBetweenLine\((\w+),\s*(\w+)\)', line)

                        if match:

                            line1, line2 = match.group(1), match.group(2)

                            # Create the variants: original and reversed

                            variants1 = [line1, line1[::-1]]

                            variants2 = [line2, line2[::-1]]

                            # Add every combination in both orders

                            for v1 in variants1:

                                for v2 in variants2:
                                    self.parallel_pairs.add((v1, v2))

                                    self.parallel_pairs.add((v2, v1))

                            print(f"Added all combinations: {self.parallel_pairs}")
                    elif line.startswith('Equal(DiameterOfCircle('):
                        # This should match a line like: Equal(DiameterOfCircle(A),10)
                        match = re.match(r'Equal\(DiameterOfCircle\((\w+)\),\s*(.+)\)', line)
                        if match:
                            circle_name, expression = match.groups()
                            expression = expression.strip()
                            print(
                                f"Found diameter expression in TEXT_CDL: DiameterOfCircle({circle_name}) = {expression}")
                            # Try to parse the expression as a number first
                            try:
                                value = float(expression)
                                print(f"Adding numeric diameter for circle {circle_name}: {value}")
                            except ValueError:
                                # Otherwise, extract any variables and parse as an algebraic expression.
                                variables = self.extract_variables(expression)
                                for var in variables:
                                    if var not in self.variables:
                                        self.variables[var] = Real(var)
                                        print(f"Created new variable for algebraic diameter: {var}")
                                value = self.parse_algebraic_expression(expression)
                                print(f"Adding algebraic diameter for circle {circle_name}: {value}")
                            diam_name = f"diameter_{circle_name}"
                            if diam_name not in self.circle_diameters:
                                self.circle_diameters[diam_name] = Real(diam_name)
                                self.solver.add(self.circle_diameters[diam_name] >= 0)
                                print(f"Created diameter variable: {diam_name}")
                            self.solver.add(self.circle_diameters[diam_name] == value)
                            print(f"Added constraint: {diam_name} == {value}")
                    elif line.startswith('Equal(MeasureOfArc('):
                        match = re.match(r'Equal\(MeasureOfArc\((\w+)\),(.+)\)', line)
                        if match:
                            arc_name, expression = match.group(1), match.group(2).strip()
                            print(f"Found arc expression in TEXT_CDL: {arc_name} = {expression}")
                            self.add_algebraic_arc(arc_name, expression)
                    elif line.startswith('Equal(Div(LengthOfLine('):
                        match = re.match(r'Equal\(Div\(LengthOfLine\((\w+)\),LengthOfLine\((\w+)\)\),(.+)\)', line)
                        if match:
                            line1, line2, expression = match.groups()
                            expression = expression.strip()
                            print(f"Found division length expression in TEXT_CDL: Div({line1},{line2}) = {expression}")

                            # Get Z3 variables for the lengths
                            try:
                                len1 = self.add_length(line1[0], line1[1])
                                len2 = self.add_length(line2[0], line2[1])
                            except IndexError:
                                print(f"Error: Invalid line name format in '{line}'. Skipping.")
                                continue  # Skip this line

                            # Try to parse the expression on the right side
                            div_val = None
                            numeric_ratio_value = None
                            try:
                                # Try Fraction first for precision (e.g., "3/2")
                                from fractions import Fraction
                                numeric_ratio_value = float(Fraction(expression))
                                div_val = numeric_ratio_value  # Use the numeric value for the constraint
                                print(f"Parsed division value as fraction: {numeric_ratio_value}")
                            except ValueError:
                                try:
                                    # Fallback: Try standard float conversion (e.g., "1.5")
                                    numeric_ratio_value = float(expression)
                                    div_val = numeric_ratio_value  # Use the numeric value
                                    print(f"Parsed division value as float: {numeric_ratio_value}")
                                except ValueError:
                                    try:
                                        # Fallback: Treat as algebraic expression (e.g., "x/2")
                                        print(f"Could not parse '{expression}' as numeric, treating as algebraic.")
                                        variables = self.extract_variables(expression)
                                        for var in variables:
                                            if var not in self.variables:
                                                self.variables[var] = Real(var)
                                        div_val = self.parse_algebraic_expression(expression)  # Z3 expression object
                                    except Exception as e_parse:
                                        print(
                                            f"Error parsing division expression '{expression}': {str(e_parse)}. Skipping constraint.")
                                        continue  # Skip adding this constraint

                            # --- Store Numeric Ratio if Found ---
                            if numeric_ratio_value is not None:
                                if not hasattr(self, 'numeric_length_ratios'):
                                    self.numeric_length_ratios = {}
                                norm_line1 = self.normalize_line_name(line1)
                                norm_line2 = self.normalize_line_name(line2)
                                # Store ratio L1/L2
                                self.numeric_length_ratios[(norm_line1, norm_line2)] = numeric_ratio_value
                                # Store ratio L2/L1 if value is non-zero
                                if abs(numeric_ratio_value) > 1e-9:
                                    self.numeric_length_ratios[(norm_line2, norm_line1)] = 1.0 / numeric_ratio_value
                                print(f"Stored known numeric ratio: {norm_line1}/{norm_line2} = {numeric_ratio_value}")
                            # --- End Storing ---

                            # Add the Z3 constraint
                            if div_val is not None:
                                # Use multiplication form: len1 == len2 * div_val
                                # This handles both numeric div_val and Z3 expression div_val
                                self.solver.add(len1 == len2 * div_val)
                                print(f"Added Z3 constraint: Length({line1}) == Length({line2}) * ({expression})")
                            else:
                                print(f"Warning: Could not determine value for constraint: {line}")
                    elif line.startswith('Equal(LengthOfLine(') and 'Mul(LengthOfLine(' in line:
                        # Handle cases like Equal(LengthOfLine(L1), Mul(LengthOfLine(L2), Value))
                        match = re.match(r'Equal\(LengthOfLine\((\w+)\),Mul\(LengthOfLine\((\w+)\),(.+)\)\)', line)
                        if match:
                            line1, line2, expression = match.groups()
                            expression = expression.strip()
                            print(
                                f"Found multiplication length expression: Length({line1}) = Length({line2}) * ({expression})")

                            # Get Z3 variables for the lengths
                            try:
                                len1 = self.add_length(line1[0], line1[1])
                                len2 = self.add_length(line2[0], line2[1])
                            except IndexError:
                                print(f"Error: Invalid line name format in '{line}'. Skipping.")
                                continue  # Skip this line

                            # Try to evaluate expression numerically
                            numeric_value = None
                            parsed_expr = None
                            try:
                                # Try simple float/fraction first
                                try:
                                    from fractions import Fraction
                                    numeric_value = float(Fraction(expression))
                                except ValueError:
                                    numeric_value = float(expression)
                                print(f"Parsed multiplier as numeric: {numeric_value}")
                                parsed_expr = numeric_value  # Use numeric value directly
                            except ValueError:
                                # Not a simple numeric value, treat as algebraic
                                print(f"Could not parse multiplier '{expression}' as numeric, treating as algebraic.")
                                try:
                                    variables = self.extract_variables(expression)
                                    for var in variables:
                                        if var not in self.variables:
                                            self.variables[var] = Real(var)
                                    parsed_expr = self.parse_algebraic_expression(expression)  # Z3 expression object
                                except Exception as e_parse:
                                    print(
                                        f"Error parsing multiplier expression '{expression}': {str(e_parse)}. Skipping constraint.")
                                    continue  # Skip adding this constraint

                            # --- Store Numeric Ratio if Found ---
                            if numeric_value is not None:
                                if not hasattr(self, 'numeric_length_ratios'):
                                    self.numeric_length_ratios = {}
                                norm_line1 = self.normalize_line_name(line1)
                                norm_line2 = self.normalize_line_name(line2)
                                # Store ratio L1/L2
                                self.numeric_length_ratios[(norm_line1, norm_line2)] = numeric_value
                                # Store ratio L2/L1 if value is non-zero
                                if abs(numeric_value) > 1e-9:
                                    self.numeric_length_ratios[(norm_line2, norm_line1)] = 1.0 / numeric_value
                                print(f"Stored known numeric ratio: {norm_line1}/{norm_line2} = {numeric_value}")
                            # --- End Storing ---

                            # Add the Z3 constraint
                            if parsed_expr is not None:
                                self.solver.add(len1 == len2 * parsed_expr)
                                print(f"Added Z3 constraint: Length({line1}) == Length({line2}) * ({expression})")
                            else:
                                print(f"Warning: Could not determine value for constraint: {line}")

                        # ... (elif block for 'Equal(LengthOfLine(' without Mul - standard numeric/algebraic assignment) ...
                        # This block should remain as you likely already have it, handling lines like:
                        # Equal(LengthOfLine(AB), 5) or Equal(LengthOfLine(CD), x)
                    elif line.startswith('Equal(LengthOfLine('):  # Assuming this is the fall-through case
                        match = re.match(r'Equal\(LengthOfLine\((\w+)\),(.+)\)', line)
                        if match:
                            line_name, expression = match.groups()
                            expression = expression.strip()
                            print(f"Found length assignment expression: Length({line_name}) = {expression}")
                            # Get (or create) the length variable
                            try:
                                length_var = self.add_length(line_name[0], line_name[1])
                            except IndexError:
                                print(f"Error: Invalid line name format '{line_name}' in '{line}'. Skipping.")
                                continue

                            # Parse and add constraint
                            parsed_val = None
                            try:
                                # Try numeric first
                                from fractions import Fraction
                                try:
                                    parsed_val = float(Fraction(expression))
                                except ValueError:
                                    parsed_val = float(expression)
                                print(f"Parsed assignment value as numeric: {parsed_val}")
                            except ValueError:
                                # Treat as algebraic
                                print(
                                    f"Could not parse assignment value '{expression}' as numeric, treating as algebraic.")
                                try:
                                    variables = self.extract_variables(expression)
                                    for var in variables:
                                        if var not in self.variables:
                                            self.variables[var] = Real(var)
                                    parsed_val = self.parse_algebraic_expression(expression)
                                except Exception as e_parse:
                                    print(
                                        f"Error parsing assignment expression '{expression}': {str(e_parse)}. Skipping constraint.")
                                    continue

                            if parsed_val is not None:
                                self.solver.add(length_var == parsed_val)
                                print(f"Added Z3 constraint: Length({line_name}) == {expression}")
                            else:
                                print(f"Warning: Could not determine value for constraint: {line}")
                    elif line.startswith("IsMedianOfTriangle("):
                        # Matches a fact like: IsMedianOfTriangle(AD,ABC)
                        match = re.match(r'IsMedianOfTriangle\((\w+),(\w{3})\)', line)
                        if match:
                            median_line, triangle = match.groups()

                            # Ensure the triangle name is valid
                            if len(triangle) != 3:
                                print(f"Error: Invalid triangle format in IsMedianOfTriangle({median_line},{triangle})")
                                continue

                            # Ensure median storage exists
                            if not hasattr(self, "medians"):
                                self.medians = []

                            # Store median information
                            self.medians.append((median_line, triangle))
                            print(f"Recorded median: IsMedianOfTriangle({median_line},{triangle})")

                            # Extract vertices
                            A, B, C = triangle

                            # Identify the midpoint of the opposite side
                            opposite_side = None
                            if median_line[0] in triangle:
                                opposite_side = [v for v in triangle if v != median_line[0]]
                            else:
                                print(f"Error: {median_line} does not start from a vertex of {triangle}")
                                continue

                            if len(opposite_side) != 2:
                                print(f"Error: Cannot determine opposite side for median {median_line}")
                                continue

                            M = median_line[1]  # Midpoint
                            X, Y = opposite_side  # The endpoints of the opposite side

                            # Store the midpoint property
                            if not hasattr(self, "midpoints"):
                                self.midpoints = {}

                            self.midpoints[(X, Y)] = M
                            self.midpoints[(Y, X)] = M

                            # Add equality constraint: XM = MY
                            len1 = self.add_length(X, M)
                            len2 = self.add_length(M, Y)
                            self.solver.add(len1 == len2)

                            # Ensure collinearity
                            collinear_points = [X, M, Y]
                            normalized_points = self.normalize_collinear_points(''.join(collinear_points))
                            if not any(set(collinear_points).issubset(set(''.join(fact))) for fact in
                                       self.collinear_facts):
                                self.collinear_facts.append(list(normalized_points))
                                self.add_collinear_fact(list(normalized_points))
                                print(f"Added collinearity constraint for median: {X}, {M}, {Y}")

                        else:
                            print("Error parsing IsMedianOfTriangle fact in TEXT_CDL.")
                    elif line.startswith('PerpendicularBetweenLine('):
                        match = re.match(r'PerpendicularBetweenLine\((\w+),\s*(\w+)\)', line)
                        if match:
                            line1, line2 = match.group(1), match.group(2)
                            print(f"Found perpendicular lines: {line1} ⊥ {line2}")
                            self.perpendicular_pairs.add((line1, line2))
                            self.perpendicular_pairs.add((line2, line1))
                            vertex = next(p for p in line1 if p in line2)
                            first_point = next(p for p in line2 if p != vertex)
                            last_point = next(p for p in line1 if p != vertex)
                            angle = f"{first_point}{vertex}{last_point}"
                            normalized_angle = self.normalize_angle_name(angle)
                            angle_var = self.add_angle(first_point, vertex, last_point)
                            self.solver.add(angle_var == 90)
                            print(f"Added 90° perpendicular angle constraint: {normalized_angle}")
                    elif line.startswith("Square("):
                        match = re.match(r"Square\((\w+)\)", line)
                        if match:
                            shape_name = match.group(1)
                            self.squares.add(shape_name)
                            self.impose_square_constraints(shape_name)
                    elif line.startswith("IsTangentOfCircle("):
                        m = re.match(r'IsTangentOfCircle\((\w+),(\w+)\)', line)
                        if m:
                            tangent_line, circle_name = m.groups()
                            self.tangent_facts.add((tangent_line, circle_name))
                            print(f"Recorded tangent: IsTangentOfCircle({tangent_line},{circle_name})")
                    elif line.startswith("IsCentreOfCircle("):
                        m = re.match(r'IsCentreOfCircle\((\w+),(\w+)\)', line)
                        if m:
                            point_name, circle_name = m.groups()
                            self.circle_centers[circle_name] = point_name
                    elif line.startswith("Rectangle("):
                        match = re.match(r"Rectangle\((\w+)\)", line)
                        if match:
                            shape_name = match.group(1)
                            # Get all cyclic variations of the rectangle name.
                            variations = get_cyclic_variations_rectangle(shape_name)
                            # Add all these variations to your rectangle set.
                            self.rectangles.update(variations)
                            print(f"Added rectangle variations: {variations}")
                    elif line.startswith("IsDiameterOfCircle("):
                        m = re.match(r'IsDiameterOfCircle\((\w+),(\w+)\)', line)
                        if m:
                            line_name, circle_name = m.groups()
                            self.is_diameter_of_circle.append((line_name, circle_name))
                    elif line.startswith('Parallelogram('):
                        match = re.match(r'Parallelogram\((\w+)\)', line)
                        if match:
                            para_name = match.group(1)
                            print(f"Found parallelogram in TEXT_CDL: {para_name}")
                            self.parallelograms.update(get_cyclic_variations(para_name))
                            print(f"Added parallelogram variations: {self.parallelograms}")
                    elif line.startswith('SimilarBetweenTriangle('):
                        match = re.match(r'SimilarBetweenTriangle\((\w+),(\w+)\)', line)
                        if match:
                            tri1, tri2 = match.groups()
                            self.add_similar_triangles(tri1, tri2)
                    elif line.startswith('RightTriangle('):
                        # Matches lines like: RightTriangle(BCA)
                        match = re.match(r'RightTriangle\((\w{3})\)', line)
                        if match:
                            triangle = match.group(1)
                            print(f"Found right triangle in TEXT_CDL: {triangle}")
                            normalized_triangle = self.normalize_triangle(triangle)

                            # Add to the set of known right triangles
                            if not hasattr(self, 'right_triangles'): self.right_triangles = set()
                            self.right_triangles.add(normalized_triangle)

                            # Assume the middle letter is the vertex with the right angle (convention)
                            # For BCA, the right angle is at C (angle BCA)
                            vertex = triangle[1]
                            p1 = triangle[0]
                            p3 = triangle[2]
                            right_angle_var = self.add_angle(p1, vertex, p3)

                            # Add the 90-degree constraint
                            self.solver.add(right_angle_var == 90)
                            print(f"Added right angle constraint based on RightTriangle fact: ∠{p1}{vertex}{p3} = 90°")
                        else:
                            print(f"Warning: Could not parse RightTriangle line: {line}")
                    elif line.startswith("Equal(AreaOfTriangle("):
                        # Matches lines like: Equal(AreaOfTriangle(ADC),9)
                        match = re.match(r'Equal\(AreaOfTriangle\((\w+)\),(.*)\)', line)
                        if match:
                            triangle, expression = match.groups()
                            expression = expression.strip()
                            normalized_triangle = ''.join(sorted(triangle))  # Normalize for lookup
                            print(f"Found triangle area in TEXT_CDL: AreaOfTriangle({triangle}) = {expression}")

                            # Create or get the area variable
                            if not hasattr(self, "triangle_areas"): self.triangle_areas = {}
                            if normalized_triangle not in self.triangle_areas:
                                self.triangle_areas[normalized_triangle] = Real(f"areaTriangle_{normalized_triangle}")
                                self.solver.add(self.triangle_areas[normalized_triangle] >= 0)
                            area_var = self.triangle_areas[normalized_triangle]

                            # Parse the expression (numeric or algebraic)
                            try:
                                eval_env = {"sqrt": math.sqrt, "pi": math.pi}
                                value = float(eval(expression, {"__builtins__": {}}, eval_env))
                                self.solver.add(area_var == value)
                                print(f"Added numeric triangle area constraint: Area({triangle}) = {value}")
                            except Exception:
                                print(f"Could not evaluate area as numeric: {expression}. Treating as algebraic.")
                                variables = self.extract_variables(expression)
                                for var in variables:
                                    if var not in self.variables: self.variables[var] = Real(var)
                                expr = self.parse_algebraic_expression(expression)
                                self.solver.add(area_var == expr)
                                print(f"Added algebraic triangle area constraint: Area({triangle}) = {expr}")
                        else:
                            print(f"Warning: Could not parse AreaOfTriangle line: {line}")



            print("\nCollected facts:")
            print("Collinear points:", self.collinear_facts)
            print("Parallel pairs:", self.parallel_pairs)
            print("Points:", list(self.points.keys()))
            # In the parse_and_verify_proof method where you process GOAL_CDL:
            if GOAL_CDL in sections:
                goal_line = sections[GOAL_CDL][0]
                # Store the raw goal line for later reference
                self.goal_line = goal_line

                # Extract goal token and type based on various goal line patterns
                # 1. Length goal
                length_match = re.search(r'Value\(LengthOfLine\((\w+)\)\)', goal_line)
                if length_match:
                    self.goal_token = length_match.group(1)
                    self.goal_type = "length"
                    print(f"Detected goal: length of line {self.goal_token}")

                # 2. Angle goal
                angle_match = re.search(r'Value\(MeasureOfAngle\((\w+)\)\)', goal_line)
                if angle_match:
                    self.goal_token = angle_match.group(1)
                    self.goal_type = "angle"
                    print(f"Detected goal: measure of angle {self.goal_token}")

                # 3. Arc measure goal
                arc_measure_match = re.search(r'Value\(MeasureOfArc\((\w+)\)\)', goal_line)
                if arc_measure_match:
                    self.goal_token = arc_measure_match.group(1)
                    self.goal_type = "arc_measure"
                    print(f"Detected goal: measure of arc {self.goal_token}")

                # 4. Arc length goal
                arc_length_match = re.search(r'Value\(LengthOfArc\((\w+)\)\)', goal_line)
                if arc_length_match:
                    self.goal_token = arc_length_match.group(1)
                    self.goal_type = "arc_length"
                    print(f"Detected goal: length of arc {self.goal_token}")

                # 5. Radius goal
                radius_match = re.search(r'Value\(RadiusOfCircle\((\w+)\)\)', goal_line)
                if radius_match:
                    self.goal_token = radius_match.group(1)
                    self.goal_type = "radius"
                    print(f"Detected goal: radius of circle {self.goal_token}")

                # 6. Cosine goal
                cosine_match = re.search(r'Value\(Cos\(MeasureOfAngle\((\w+)\)\)\)', goal_line)
                if cosine_match:
                    self.goal_token = cosine_match.group(1)
                    self.goal_type = "cosine"
                    print(f"Detected goal: cosine of angle {self.goal_token}")

                # 7. Sine goal
                sine_match = re.search(r'Value\(Sin\(MeasureOfAngle\((\w+)\)\)\)', goal_line)
                if sine_match:
                    self.goal_token = sine_match.group(1)
                    self.goal_type = "sine"
                    print(f"Detected goal: sine of angle {self.goal_token}")

                # 8. Sum of lengths
                sum_lengths_match = re.search(r'Value\(Add\(LengthOfLine\((\w+)\),LengthOfLine\((\w+)\)\)\)', goal_line)
                if sum_lengths_match:
                    self.goal_token = f"{sum_lengths_match.group(1)}+{sum_lengths_match.group(2)}"
                    self.goal_type = "sum"
                    print(f"Detected goal: sum of lines {self.goal_token}")

                # 9. Ratio of lengths
                length_div_match = re.search(r'Value\(Div\(LengthOfLine\((\w+)\),LengthOfLine\((\w+)\)\)\)', goal_line)
                if length_div_match:
                    self.goal_token = f"{length_div_match.group(1)}/{length_div_match.group(2)}"
                    self.goal_type = "ratio"
                    print(f"Detected goal: ratio of lines {self.goal_token}")

                # 10. Triangle perimeter
                perimeter_match = re.search(r'Value\(PerimeterOfTriangle\((\w+)\)\)', goal_line)
                if perimeter_match:
                    self.goal_token = perimeter_match.group(1)
                    self.goal_type = "perimeter"
                    print(f"Detected goal: perimeter of triangle {self.goal_token}")

                # 11. Quadrilateral area
                quad_area_match = re.search(r'Value\(AreaOfQuadrilateral\((\w+)\)\)', goal_line)
                if quad_area_match:
                    self.goal_token = quad_area_match.group(1)
                    self.goal_type = "quad_area"
                    print(f"Detected goal: area of quadrilateral {self.goal_token}")

                # 12. Triangle area
                triangle_area_match = re.search(r'Value\(AreaOfTriangle\((\w+)\)\)', goal_line)
                if triangle_area_match:
                    self.goal_token = triangle_area_match.group(1)
                    self.goal_type = "triangle_area"
                    print(f"Detected goal: area of triangle {self.goal_token}")

                # 13. Generic variable goal
                general_match = re.search(r'Value\((.+)\)', goal_line)
                if general_match and not hasattr(self, 'goal_token'):
                    self.goal_token = general_match.group(1)
                    self.goal_type = "general"
                    print(f"Detected general goal: {self.goal_token}")
            # Process theorem sequence
            # Inside parse_and_verify_proof method
            # Process theorem sequence before verifying goal
            if THEOREM_SEQUENCE in sections:
                sequence_text = '\n'.join(sections[THEOREM_SEQUENCE])
                # Split into individual steps
                steps = [step.strip() for step in sequence_text.split('\n') if step.strip()]

                for step in steps:
                    # Split the step into its components using semicolon
                    parts = step.split(';')
                    if len(parts) >= 4:  # Should have step number, theorem call, premise, and conclusion
                        # Extract theorem name and arguments
                        step_number = parts[0].strip()
                        theorem_part = parts[1].strip()
                        theorem_match = re.search(r'(\w+)\((.*?)\)', theorem_part)

                        if theorem_match:
                            theorem_name = theorem_match.group(1)
                            args = [arg.strip() for arg in theorem_match.group(2).split(',')]

                            # Get premise and conclusion
                            premise = parts[2].strip()
                            conclusions = eval(parts[3].strip())  # This will parse the list string

                            self.theorem_sequence.append({
                                "step_number": step_number,
                                "theorem_name": theorem_name,
                                "args": args,
                                "premise": premise,
                                "conclusions": conclusions
                            })

                            print(f"\nTrying to process theorem: {theorem_name} with:")
                            print(f"Arguments: {args}")
                            print(f"Premise: '{premise}'")
                            print(f"Conclusions: {conclusions}")

                            # Validate premises first
                            # Validate premises first
                            # Validate premises first
                            is_valid, error = self.validate_theorem_premises(theorem_name, args, premise)
                            if not is_valid:
                                print(f"\nError in {error.tier.name}:")
                                # --- MODIFICATION START ---
                                if error.tier == ErrorTier.TIER1_THEOREM_CALL_SYNTAX_VIOLATION:
                                    # For TIER1, prioritize details for the feedback message
                                    error_content = error.details if error.details else error.message
                                    # Print details to console as well for clarity
                                    print(f"Details: {error_content}")
                                    # Construct the feedback string using the prioritized content
                                    feedback_message = f"Error in {error.tier.name}: {error_content}"
                                    # Return the specific feedback for TIER1
                                    return False, feedback_message
                                else:
                                    # For TIER2/TIER3, print message first, then details if available
                                    print(f"Message: {error.message}")
                                    if error.details:
                                        print(f"Details: {error.details}")
                                # --- MODIFICATION END ---

                                if error.tier == ErrorTier.TIER2_PREMISE_VIOLATION:
                                    # Use the special formatted feedback for premise errors
                                    return False, self.generate_premise_error_feedback(theorem_name, args, premise,
                                                                                       conclusions, error)
                                else:
                                    return False, f"Error in {error.tier.name}: {error.message}"

                            # Then process theorem step
                            # Then process theorem step
                            # Then process theorem step
                            error = self.adding_conclution(theorem_name, args, premise, conclusions)
                            if error:
                                print(f"\nError in {error.tier.name}:")
                                # --- MODIFICATION START ---
                                if error.tier == ErrorTier.TIER1_THEOREM_CALL_SYNTAX_VIOLATION:
                                    # For TIER1, prioritize details for the feedback message
                                    error_content = error.details if error.details else error.message
                                    # Print details to console as well for clarity
                                    print(f"Details: {error_content}")
                                    # Construct the feedback string using the prioritized content
                                    feedback_message = f"Error in {error.tier.name}: {error_content}"
                                    # Return the specific feedback for TIER1
                                    return False, feedback_message
                                else:
                                    # For TIER2/TIER3, print message first, then details if available
                                    print(f"Message: {error.message}")
                                    if error.details:
                                        print(f"Details: {error.details}")
                                # --- MODIFICATION END ---

                                if error.tier == ErrorTier.TIER2_PREMISE_VIOLATION:
                                    # Use the special formatted feedback for premise errors
                                    return False, self.generate_premise_error_feedback(theorem_name, args, premise,
                                                                                       conclusions, error)
                                else:
                                    return False, f"Error in {error.tier.name}: {error.message}"

            if GOAL_CDL in sections:
                goal_line = sections[GOAL_CDL][0]

                def parse_special_answer(answer_str):
                    """Parse answer strings including complex trigonometric expressions."""
                    import math
                    import re

                    # Store original symbolic form
                    original_symbolic = answer_str.strip()

                    # Remove whitespace
                    answer_str = answer_str.strip()

                    # Handle trig expressions with pi/180 conversion
                    if 'sin(' in answer_str.lower() or 'cos(' in answer_str.lower() or 'tan(' in answer_str.lower():
                        try:
                            # Replace pi with math.pi
                            modified_str = answer_str.replace('pi', 'math.pi')

                            # Create a safe environment with only math functions
                            safe_globals = {
                                'math': math,
                                'sin': math.sin,
                                'cos': math.cos,
                                'tan': math.tan,
                                'sqrt': math.sqrt
                            }

                            # Try direct evaluation with math functions
                            return float(eval(modified_str, {"__builtins__": {}}, safe_globals)), original_symbolic
                        except Exception as e:
                            print(f"Error evaluating trig expression: {e}")
                            # Continue to other methods if this fails

                    # Handle √ symbol format: 6(√6-1)
                    if '√' in answer_str:
                        # Handle pattern like "6(√6-1)"
                        pattern = r'(\d+)\(√(\d+)(-|\+)(\d+)\)'
                        match = re.match(pattern, answer_str)
                        if match:
                            a, b, op, c = match.groups()
                            a, b, c = float(a), float(b), float(c)
                            if op == '-':
                                return a * (math.sqrt(b) - c), original_symbolic
                            else:  # op == '+'
                                return a * (math.sqrt(b) + c), original_symbolic

                        # Handle pattern like "2√13"
                        pattern = r'(\d*)(√\d+)'
                        match = re.match(pattern, answer_str)
                        if match:
                            coef, sqrt_part = match.groups()
                            coef = 1 if coef == '' else float(coef)
                            sqrt_str = sqrt_part.replace('√', 'math.sqrt(') + ')'
                            try:
                                sqrt_val = eval(sqrt_str, {"math": math})
                                return coef * sqrt_val, original_symbolic
                            except Exception as e:
                                print(f"Error evaluating {sqrt_str}: {e}")
                                pass

                        # General replacement of √ symbol
                        try:
                            modified_str = re.sub(r'(\d*)√(\d+)', r'\1*math.sqrt(\2)', answer_str)
                            # Handle implicit multiplication
                            modified_str = re.sub(r'(\d+)\(', r'\1*(', modified_str)
                            return float(eval(modified_str, {"math": math})), original_symbolic
                        except Exception as e:
                            print(f"Error evaluating modified string '{modified_str}': {e}")
                            pass
                    if 'π' in answer_str:
                        # Pattern for (aπ)/b format
                        pattern = r'\((\d+)π\)/(\d+)'
                        match = re.match(pattern, answer_str)
                        if match:
                            a, b = match.groups()
                            a, b = float(a), float(b)
                            return (a * math.pi) / b, original_symbolic

                        # Pattern for aπ/b format (without parentheses)
                        pattern = r'(\d+)π/(\d+)'
                        match = re.match(pattern, answer_str)
                        if match:
                            a, b = match.groups()
                            a, b = float(a), float(b)
                            return (a * math.pi) / b, original_symbolic

                        # Handle other π expressions with general replacement
                        try:
                            # Replace π with math.pi for evaluation
                            modified_str = answer_str.replace('π', '*math.pi')
                            # Handle implicit multiplication and edge cases
                            modified_str = re.sub(r'(\d+)\(', r'\1*(', modified_str)
                            return float(eval(modified_str, {"math": math})), original_symbolic
                        except Exception as e:
                            print(f"Error evaluating π expression '{modified_str}': {e}")
                            pass
                    # Standard eval with math functions
                    try:
                        safe_globals = {
                            "pi": math.pi,
                            "sqrt": math.sqrt,
                            "sin": math.sin,
                            "cos": math.cos,
                            "tan": math.tan
                        }
                        return float(eval(answer_str, {"__builtins__": {}}, safe_globals)), original_symbolic
                    except Exception as e:
                        print(f"Error in standard eval: {e}")
                        # Fall back to Fraction
                        from fractions import Fraction
                        try:
                            return float(Fraction(answer_str)), original_symbolic
                        except Exception as e:
                            print(f"Error with Fraction conversion: {e}")
                            # Try numerical approximation for complex expressions
                            try:
                                # Replace mathematical functions with their math module equivalents
                                answer_str = answer_str.replace('sin', 'math.sin')
                                answer_str = answer_str.replace('cos', 'math.cos')
                                answer_str = answer_str.replace('tan', 'math.tan')
                                answer_str = answer_str.replace('pi', 'math.pi')

                                # Evaluate with a safe environment
                                result = eval(answer_str, {"__builtins__": {}}, {"math": math})
                                return float(result), original_symbolic
                            except Exception as e:
                                print(f"Error with numerical approximation: {e}")

                                # NEW CODE: Add SymPy as the last resort fallback method
                                try:
                                    # Import sympy only when needed
                                    from sympy import symbols, sympify, pi, N

                                    # Replace symbols with SymPy-compatible notation
                                    sympy_compatible = answer_str
                                    sympy_compatible = sympy_compatible.replace('π', 'pi')
                                    sympy_compatible = sympy_compatible.replace('√', 'sqrt')

                                    # Parse with SymPy's powerful expression parser
                                    expr = sympify(sympy_compatible)

                                    # Convert to floating point
                                    numeric_value = float(N(expr))

                                    print(f"Successfully parsed with SymPy: {numeric_value}")
                                    return numeric_value, original_symbolic
                                except Exception as e:
                                    print(f"Error parsing with SymPy: {e}")
                                    # If SymPy also fails, give up and raise the exception
                                    raise ValueError(f"Could not parse: {answer_str}")

                answer_str = sections[ANSWER][0].strip() if (ANSWER in sections and sections[ANSWER]) else None
                if answer_str is None:
                    return False, "No answer provided in ANSWER section."

                # Check for algebraic variables before trying to parse
                if self.contains_algebraic_variables(answer_str):
                    return False, "The final answer should be a numeric answer, you gave an expression with algebraic variable. Please fix your proof."

                try:
                    model_answer_numeric, model_answer_symbolic = parse_special_answer(answer_str)
                except Exception as e:
                    return False, f"Error parsing answer '{answer_str}': {str(e)}"
                    # Arc measure goal: Value(MeasureOfArc(X))
                epsilon = 1e-8  # Common epsilon value for all goals
                # Check against GT_ANSWER - if this fails, return early
                gt_check_result, gt_check_feedback = check_gt_answer(model_answer_numeric, model_answer_symbolic)
                if not gt_check_result:
                    return gt_check_result, gt_check_feedback
                arc_measure_match = re.search(r'Value\(MeasureOfArc\((\w+)\)\)', goal_line)
                if arc_measure_match:
                    arc_token = arc_measure_match.group(1)
                    print(f"\nGoal arc measure: {arc_token}")

                    normalized_arc = self.normalize_arc(arc_token)
                    arc_var_name = f"arc_{normalized_arc}"

                    if arc_var_name not in self.arcs:
                        error_msg = f"Arc {arc_token} is not defined in the system"
                        print(f"Error: {error_msg}")
                        return False, error_msg

                    arc_var = self.arcs[arc_var_name]
                    success, value, status = self.check_value_constraint(arc_var, model_answer_numeric)

                    if success:
                        return True, ""
                    else:
                        # Generate detailed feedback report
                        detailed_feedback = self.generate_detailed_feedback(
                            goal_type="arc_measure",
                            goal_token=arc_token,
                            model_answer=model_answer_symbolic,
                            verifier_expected_answer=value,
                            status=status
                        )
                        print(f"Detailed feedback generated for arc measure goal.")
                        return False, detailed_feedback

                # 2. Arc length goal: Value(LengthOfArc(X))
                arc_length_match = re.search(r'Value\(LengthOfArc\((\w+)\)\)', goal_line)
                if arc_length_match:
                    arc_token = arc_length_match.group(1)
                    print(f"\nGoal arc length: {arc_token}")


                    normalized_arc = self.normalize_arc(arc_token)
                    length_var_name = f"lengthArc_{normalized_arc}"
                    arc_length_var = Real(length_var_name)

                    success, value, status = self.check_value_constraint(arc_length_var, model_answer_numeric)

                    if success:
                        print(f"Success: Arc length {arc_token} is uniquely determined to be {model_answer_numeric}.")
                        return True, ""
                    else:
                        # Generate detailed feedback report
                        detailed_feedback = self.generate_detailed_feedback(
                            goal_type="arc_length",
                            goal_token=arc_token,
                            model_answer=model_answer_symbolic,
                            verifier_expected_answer=value,
                            status=status
                        )
                        print(f"Detailed feedback generated for arc length goal.")
                        return False, detailed_feedback

                radius_match = re.search(r'Value\(RadiusOfCircle\((\w+)\)\)', goal_line)
                if radius_match:
                    circle_token = radius_match.group(1)
                    print(f"\nGoal radius of circle: {circle_token}")

                    # Check if the circle has been defined
                    if not hasattr(self, 'circle_radii'):
                        self.circle_radii = {}

                    # Get or create the radius variable
                    if circle_token not in self.circle_radii:
                        radius_var = Real(f"radius_{circle_token}")
                        self.circle_radii[circle_token] = radius_var
                        self.solver.add(radius_var > 0)  # Radius must be positive
                    else:
                        radius_var = self.circle_radii[circle_token]

                    # Check if the value matches the expected answer
                    success, value, status = self.check_value_constraint(radius_var, model_answer_numeric)

                    if success:
                        print(
                            f"Success: Radius of circle {circle_token} is uniquely determined to be {model_answer_numeric}.")
                        return True, ""
                    else:
                        # Generate detailed feedback
                        detailed_feedback = self.generate_detailed_feedback(
                            goal_type="radius",
                            goal_token=circle_token,
                            model_answer=model_answer_symbolic,
                            verifier_expected_answer=value,
                            status=status
                        )
                        print(f"Detailed feedback generated for circle radius goal.")
                        return False, detailed_feedback

                # Add this new goal handler in the parse_and_verify_proof method
                # (place it before the general_match block, after the radius_match handler we just added)

                # Reciprocal sum goal: Value(Add(Div(1,LengthOfLine(X)),Div(1,LengthOfLine(Y))))
                reciprocal_sum_match = re.search(
                    r'Value\(Add\(Div\(1,LengthOfLine\((\w+)\)\),Div\(1,LengthOfLine\((\w+)\)\)\)\)', goal_line)
                if reciprocal_sum_match:
                    line1 = reciprocal_sum_match.group(1)  # First line (e.g., "AM")
                    line2 = reciprocal_sum_match.group(2)  # Second line (e.g., "AN")

                    print(f"\nGoal reciprocal sum: 1/LengthOfLine({line1}) + 1/LengthOfLine({line2})")
                    goal_token = f"1/{line1}+1/{line2}"  # For feedback reporting

                    # Get the length variables for both lines
                    len1 = self.add_length(line1[0], line1[1])
                    len2 = self.add_length(line2[0], line2[1])

                    if self.solver.check() == sat:
                        model = self.solver.model()
                        try:
                            # Evaluate the lengths
                            len1_val = float(model.eval(len1).as_decimal(10).rstrip('?'))
                            len2_val = float(model.eval(len2).as_decimal(10).rstrip('?'))

                            # Check for division by zero
                            if abs(len1_val) < epsilon or abs(len2_val) < epsilon:
                                error_msg = "Division by zero in reciprocal sum"
                                print(f"Error: {error_msg}")
                                detailed_feedback = self.generate_detailed_feedback(
                                    goal_type="general",
                                    goal_token=goal_token,
                                    model_answer=model_answer_symbolic,
                                    status="insufficient_info",
                                    additional_info=f"Error: {error_msg}. Your proof constrains {line1} = {len1_val} or {line2} = {len2_val}, which would cause division by zero."
                                )
                                return False, detailed_feedback

                            # Calculate the expected answer: 1/len1 + 1/len2
                            verifier_expected_answer = (1.0 / len1_val) + (1.0 / len2_val)

                            # Check if the lengths are uniquely determined
                            temp_solver = Solver()
                            for c in self.solver.assertions():
                                temp_solver.add(c)

                            # Try to find alternative values for the lengths
                            temp_solver.add(Or(
                                len1 < len1_val - epsilon,
                                len1 > len1_val + epsilon,
                                len2 < len2_val - epsilon,
                                len2 > len2_val + epsilon
                            ))

                            if temp_solver.check() == sat:
                                # Multiple values possible
                                alt_model = temp_solver.model()
                                alt_len1_val = float(alt_model.eval(len1).as_decimal(10).rstrip('?'))
                                alt_len2_val = float(alt_model.eval(len2).as_decimal(10).rstrip('?'))

                                # Check for division by zero in the alternative solution
                                if abs(alt_len1_val) < epsilon or abs(alt_len2_val) < epsilon:
                                    print("Alternative solution involves division by zero, ignoring")
                                else:
                                    alt_sum = (1.0 / alt_len1_val) + (1.0 / alt_len2_val)

                                    # If the alternative sum is very close to the expected sum,
                                    # then the reciprocal sum might still be uniquely determined
                                    if abs(alt_sum - verifier_expected_answer) < epsilon:
                                        print(f"Alternative lengths give the same sum, continuing validation")
                                    else:
                                        # Generate detailed feedback for multiple values
                                        detailed_feedback = self.generate_detailed_feedback(
                                            goal_type="general",
                                            goal_token=goal_token,
                                            model_answer=model_answer_symbolic,
                                            verifier_expected_answer=None,
                                            status="multiple_values",
                                            additional_info=f"Your proof doesn't uniquely determine the value.\n"
                                        )
                                        return False, detailed_feedback

                            # Check if the computed value matches the expected answer
                            if abs(verifier_expected_answer - model_answer_numeric) < epsilon:
                                return True, ""
                            else:
                                # Generate detailed feedback for incompatible values
                                detailed_feedback = self.generate_detailed_feedback(
                                    goal_type="general",
                                    goal_token=goal_token,
                                    model_answer=model_answer_symbolic,
                                    verifier_expected_answer=verifier_expected_answer,
                                    status="incompatible",
                                    additional_info=f"Your proof constrains the lengths to {line1} = {len1_val} and {line2} = {len2_val},\n" +
                                                    f"which gives 1/{line1} + 1/{line2} = {verifier_expected_answer}, not {model_answer_numeric}."
                                )
                                return False, detailed_feedback

                        except Exception as e:
                            error_msg = f"Error calculating reciprocal sum: {str(e)}"
                            print(f"Error: {error_msg}")
                            return False, error_msg
                    else:
                        # Generate detailed feedback for unsatisfiable system
                        detailed_feedback = self.generate_detailed_feedback(
                            goal_type="general",
                            goal_token=goal_token,
                            model_answer=model_answer_symbolic,
                            status="unsatisfiable"
                        )
                        return False, detailed_feedback



                triangle_area_match = re.search(r'Value\(AreaOfTriangle\((\w+)\)\)', goal_line)
                if triangle_area_match:
                    triangle_name = triangle_area_match.group(1)  # e.g., "CDB"
                    print(f"\nGoal type: Triangle Area ({triangle_name})")
                    print(f"Expected area: {model_answer_numeric}")

                    # Normalize the triangle name for dictionary lookup
                    normalized_triangle = ''.join(sorted(triangle_name))

                    # Check if the area variable exists
                    if not hasattr(self, "triangle_areas") or normalized_triangle not in self.triangle_areas:
                        error_msg = f"Area variable for triangle {triangle_name} (normalized: {normalized_triangle}) not defined by any theorem."
                        print(f"Error: {error_msg}")
                        # Known areas for debugging:
                        known_areas = list(getattr(self, 'triangle_areas', {}).keys())
                        print(f"Known triangle areas: {known_areas}")
                        return False, self.generate_detailed_feedback("triangle_area", triangle_name,
                                                                      model_answer_symbolic,
                                                                      status="insufficient_info",
                                                                      additional_info=error_msg)

                    triangle_area_var = self.triangle_areas[normalized_triangle]
                    self.solver.add(triangle_area_var>0)
                    # Check if the value matches the expected answer
                    success, value, status = self.check_value_constraint(triangle_area_var, model_answer_numeric, epsilon=epsilon)

                    if success:
                        print(f"Success: The area of triangle {triangle_name} is uniquely determined to be {model_answer_numeric}.")
                        return True, ""
                    else:
                        # Generate detailed feedback report
                        detailed_feedback = self.generate_detailed_feedback(
                            goal_type="triangle_area",
                            goal_token=triangle_name,
                            model_answer=model_answer_symbolic,
                            verifier_expected_answer=value,
                            status=status
                        )
                        print(f"Detailed feedback generated for triangle area goal.")
                        return False, detailed_feedback
                    # --- END OF ADDED BLOCK ---




                # Add this after other goal type checks like arc_measure, length, etc.
                quad_perimeter_match = re.search(r'Value\(PerimeterOfQuadrilateral\((\w+)\)\)', goal_line)
                if quad_perimeter_match:
                    quad_name = quad_perimeter_match.group(1)
                    print(f"\nGoal quadrilateral perimeter: {quad_name}")
                    print(f"Expected perimeter: {model_answer_numeric}")

                    # Create or get the perimeter variable for this quadrilateral
                    if not hasattr(self, "quadrilateral_perimeters"):
                        self.quadrilateral_perimeters = {}

                    if quad_name not in self.quadrilateral_perimeters:
                        perimeter_var = Real(f"perimeter_{quad_name}")
                        self.quadrilateral_perimeters[quad_name] = perimeter_var
                    else:
                        perimeter_var = self.quadrilateral_perimeters[quad_name]

                    # Check if the perimeter matches the model answer
                    success, value, status = self.check_value_constraint(perimeter_var, model_answer_numeric)

                    if success:
                        print(
                            f"Success: Quadrilateral perimeter {quad_name} is uniquely determined to be {model_answer_numeric}.")
                        return True, ""
                    else:
                        # Generate detailed feedback report
                        detailed_feedback = self.generate_detailed_feedback(
                            goal_type="quadrilateral_perimeter",
                            goal_token=quad_name,
                            model_answer=model_answer_symbolic,
                            verifier_expected_answer=value,
                            status=status
                        )
                        print(f"Detailed feedback generated for quadrilateral perimeter goal.")
                        return False, detailed_feedback

                sum_angles_match = re.search(r'Value\(Add\(MeasureOfAngle\((\w+)\),MeasureOfAngle\((\w+)\)\)\)',
                                             goal_line)
                if sum_angles_match:
                    angle1_token = sum_angles_match.group(1)
                    angle2_token = sum_angles_match.group(2)
                    goal_token = f"{angle1_token}+{angle2_token}"  # For feedback reporting
                    print(f"\nGoal type: Sum of Angles ({goal_token})")

                    # Get the Z3 variables for the angles
                    angle1_var = self.add_angle(angle1_token[0], angle1_token[1], angle1_token[2])
                    angle2_var = self.add_angle(angle2_token[0], angle2_token[1], angle2_token[2])

                    # Create the sum expression
                    sum_expr = angle1_var + angle2_var

                    # Check if the value matches the expected answer
                    success, value, status = self.check_value_constraint(sum_expr, model_answer_numeric, epsilon=epsilon)

                    if success:

                        return True, ""
                    else:
                        # Generate detailed feedback report
                        detailed_feedback = self.generate_detailed_feedback(
                            goal_type="sum_angle",  # Use a descriptive type
                            goal_token=goal_token,
                            model_answer=model_answer_symbolic,
                            verifier_expected_answer=value,
                            status=status,
                            # Add info about individual angles if helpful
                            additional_info=f"Angle 1: {angle1_token}\nAngle 2: {angle2_token}"
                        )
                        print(f"Detailed feedback generated for sum of angles goal.")
                        return False, detailed_feedback

                sum_lengths_match = re.search(r'Value\(Add\(LengthOfLine\((\w+)\),LengthOfLine\((\w+)\)\)\)', goal_line)
                if sum_lengths_match:
                    line1 = sum_lengths_match.group(1)
                    line2 = sum_lengths_match.group(2)

                    print(f"\nGoal sum of lengths: LengthOfLine({line1}) + LengthOfLine({line2})")


                    len1 = self.add_length(line1[0], line1[1])
                    len2 = self.add_length(line2[0], line2[1])
                    sum_expr = len1 + len2

                    success, value, status = self.check_value_constraint(sum_expr, model_answer_numeric)

                    if success:
                        return True, ""
                    else:
                        # Generate detailed feedback report
                        goal_token = f"{line1}+{line2}"  # Create a combined token
                        detailed_feedback = self.generate_detailed_feedback(
                            goal_type="sum",
                            goal_token=goal_token,
                            model_answer=model_answer_symbolic,
                            verifier_expected_answer=value,
                            status=status
                        )
                        print(f"Detailed feedback generated for sum of lengths goal.")
                        return False, detailed_feedback

                # Cosine goal: Value(Cos(MeasureOfAngle(XXX)))
                # Cosine goal: Value(Cos(MeasureOfAngle(XXX)))
                cosine_match = re.search(r'Value\(Cos\(MeasureOfAngle\((\w+)\)\)\)', goal_line)
                if cosine_match:
                    angle_token = cosine_match.group(1)
                    print(f"\nGoal cosine: Cos(MeasureOfAngle({angle_token}))")

                    success, value, status = self.evaluate_trig_function("cos", angle_token, model_answer_numeric)

                    if success:
                        return True, ""
                    else:
                        # Generate detailed feedback report
                        detailed_feedback = self.generate_detailed_feedback(
                            goal_type="cosine",
                            goal_token=angle_token,
                            model_answer=model_answer_symbolic,
                            verifier_expected_answer=value,
                            status=status
                        )
                        print(f"Detailed feedback generated for cosine goal.")
                        return False, detailed_feedback

                sin_match = re.search(r'Value\(Sin\(MeasureOfAngle\((\w+)\)\)\)', goal_line)
                if sin_match:
                    angle_token = sin_match.group(1)
                    print(f"\nGoal sine: Sin(MeasureOfAngle({angle_token}))")

                    success, value, status = self.evaluate_trig_function("sin", angle_token, model_answer_numeric)

                    if success:
                        return True, ""
                    else:
                        # Generate detailed feedback report
                        detailed_feedback = self.generate_detailed_feedback(
                            goal_type="sine",
                            goal_token=angle_token,
                            model_answer=model_answer_symbolic,
                            verifier_expected_answer=value,
                            status=status
                        )
                        print(f"Detailed feedback generated for sine goal.")
                        return False, detailed_feedback

                # Sine goal and other goal types would follow a similar pattern, using the common
                # check_value_constraint function where possible and handling special cases as needed
                # 6. Division of lengths goal: Value(Div(LengthOfLine(AF),LengthOfLine(AC)))
                length_div_match = re.search(r'Value\(Div\(LengthOfLine\((\w+)\),LengthOfLine\((\w+)\)\)\)', goal_line)
                if length_div_match:
                    line1 = length_div_match.group(1)  # Numerator line
                    line2 = length_div_match.group(2)  # Denominator line

                    print(f"\nGoal division of lengths: Div(LengthOfLine({line1}),LengthOfLine({line2}))")

                    len1 = self.add_length(line1[0], line1[1])
                    len2 = self.add_length(line2[0], line2[1])

                    if self.solver.check() == sat:
                        model = self.solver.model()
                        try:
                            val1 = float(model.eval(len1).as_decimal(10).rstrip('?'))
                            val2 = float(model.eval(len2).as_decimal(10).rstrip('?'))

                            # Check for division by zero
                            if abs(val2) < epsilon:
                                error_msg = "Division by zero in length ratio"
                                print("Error: Division by zero in length ratio")
                                return False, error_msg

                            verifier_expected_answer = val1 / val2

                            # Check if the division is uniquely determined
                            temp_solver = Solver()
                            for c in self.solver.assertions():
                                temp_solver.add(c)

                            # We want to check if len1/len2 can have a different value
                            temp_solver.add(
                                Or(
                                    len1 < (model_answer_numeric - epsilon) * len2,
                                    len1 > (model_answer_numeric + epsilon) * len2
                                )
                            )

                            if temp_solver.check() == sat:
                                alt_model = temp_solver.model()
                                alt_val1 = float(alt_model.eval(len1).as_decimal(10).rstrip('?'))
                                alt_val2 = float(alt_model.eval(len2).as_decimal(10).rstrip('?'))

                                if abs(alt_val2) < epsilon:
                                    # Skip this alternative since it involves division by zero
                                    print("Note: Found an alternative solution but it involves division by zero")
                                    alt_ratio = None
                                    status = "multiple_values"
                                else:
                                    alt_ratio = alt_val1 / alt_val2
                                    status = "multiple_values"

                                # Generate detailed feedback for multiple values
                                goal_token = f"{line1}/{line2}"
                                detailed_feedback = self.generate_detailed_feedback(
                                    goal_type="ratio",
                                    goal_token=goal_token,
                                    model_answer=model_answer_symbolic,
                                    verifier_expected_answer=alt_ratio,
                                    status=status,
                                    additional_info=""
                                )
                                print(f"Detailed feedback generated for division goal.")
                                return False, detailed_feedback

                            # Check if computed value matches expected value
                            if abs(verifier_expected_answer - model_answer_numeric) >= epsilon:
                                # Generate detailed feedback for incompatible value
                                goal_token = f"{line1}/{line2}"
                                detailed_feedback = self.generate_detailed_feedback(
                                    goal_type="ratio",
                                    goal_token=goal_token,
                                    model_answer=model_answer_symbolic,
                                    verifier_expected_answer=verifier_expected_answer,
                                    status="incompatible",
                                    additional_info=f"Your proof constrains the ratio to {verifier_expected_answer:.6f}"
                                )
                                print(f"Detailed feedback generated for division goal.")
                                return False, detailed_feedback


                            return True, ""
                        except Exception as e:
                            error_msg = f"Error converting length values: {str(e)}"
                            print("Error converting length values:", e)
                            return False, error_msg
                    else:
                        # Generate detailed feedback for unsatisfiable
                        goal_token = f"{line1}/{line2}"
                        detailed_feedback = self.generate_detailed_feedback(
                            goal_type="ratio",
                            goal_token=goal_token,
                            model_answer=model_answer_symbolic,
                            status="unsatisfiable"
                        )
                        print(f"Detailed feedback generated for division goal.")
                        return False, detailed_feedback

                perimeter_match = re.search(r'Value\(PerimeterOfTriangle\((\w+)\)\)', goal_line)
                if perimeter_match:
                    triangle = perimeter_match.group(1)
                    print(f"\nDetected perimeter goal: PerimeterOfTriangle({triangle})")
                    print(f"\nGoal triangle perimeter: {triangle}")

                    if triangle in self.triangle_perimeters:
                        perimeter_var = self.triangle_perimeters[triangle]
                    else:
                        perimeter_var = self.calculate_perimeter(triangle)
                        self.triangle_perimeters[triangle] = perimeter_var

                    success, value, status = self.check_value_constraint(perimeter_var, model_answer_numeric)

                    if success:
                        return True, ""
                    else:
                        # Generate detailed feedback report
                        detailed_feedback = self.generate_detailed_feedback(
                            goal_type="perimeter",
                            goal_token=triangle,
                            model_answer=model_answer_symbolic,
                            verifier_expected_answer=value,
                            status=status,
                            additional_info=f"Triangle sides:\n" +
                                            f"  {triangle[0]}{triangle[1]}: {self.add_length(triangle[0], triangle[1])}\n" +
                                            f"  {triangle[1]}{triangle[2]}: {self.add_length(triangle[1], triangle[2])}\n" +
                                            f"  {triangle[2]}{triangle[0]}: {self.add_length(triangle[2], triangle[0])}"
                        )
                        print(f"Detailed feedback generated for perimeter goal.")
                        return False, detailed_feedback

                    # 8. Length goal: Value(LengthOfLine(AB))
                length_match = re.search(r'Value\(LengthOfLine\((\w+)\)\)', goal_line)
                if length_match:
                    line_name = length_match.group(1)
                    print(f"\nGoal line: {line_name}")

                    # Get the length variable
                    length_var = self.add_length(line_name[0], line_name[1])

                    success, value, status = self.check_value_constraint(length_var, model_answer_numeric)

                    if success:
                        return True, ""
                    else:
                        # Generate detailed feedback report
                        detailed_feedback = self.generate_detailed_feedback(
                            goal_type="length",
                            goal_token=line_name,
                            model_answer=model_answer_symbolic,
                            verifier_expected_answer=value,
                            status=status
                        )
                        print(f"Detailed feedback generated for length goal.")
                        return False, detailed_feedback

                angle_match = re.search(r'Value\(MeasureOfAngle\((\w+)\)\)', goal_line)
                if angle_match:
                    goal_angle = angle_match.group(1)
                    print(f"\nGoal angle: {goal_angle}")

                    angle_var = self.add_angle(goal_angle[0], goal_angle[1], goal_angle[2])

                    success, value, status = self.check_value_constraint(angle_var, model_answer_numeric)

                    if success:
                        return True, ""
                    else:
                        # Generate detailed feedback report
                        detailed_feedback = self.generate_detailed_feedback(
                            goal_type="angle",
                            goal_token=goal_angle,
                            model_answer=model_answer_symbolic,
                            verifier_expected_answer=value,
                            status=status
                        )
                        print(f"Detailed feedback generated for angle goal.")
                        return False, detailed_feedback

                    # 10. Quadrilateral area goal: Value(AreaOfQuadrilateral(ABCD))
                quad_area_match = re.search(r'Value\(AreaOfQuadrilateral\((\w+)\)\)', goal_line)
                if quad_area_match:
                    quad_name = quad_area_match.group(1)
                    print(f"\nDetected quadrilateral area goal: AreaOfQuadrilateral({quad_name})")
                    print(f"\nGoal quadrilateral area: {quad_name}")

                    if quad_name in self.quad_areas:
                        quad_area_var = self.quad_areas[quad_name]
                    else:
                        quad_area_var = Real(f"AreaOfQuadrilateral_{quad_name}")
                        self.quad_areas[quad_name] = quad_area_var

                    success, value, status = self.check_value_constraint(quad_area_var, model_answer_numeric)

                    if success:

                        return True, ""
                    else:
                        # Generate detailed feedback report
                        detailed_feedback = self.generate_detailed_feedback(
                            goal_type="quad_area",
                            goal_token=quad_name,
                            model_answer=model_answer_symbolic,
                            verifier_expected_answer=value,
                            status=status
                        )
                        print(f"Detailed feedback generated for quadrilateral area goal.")
                        return False, detailed_feedback
                general_match = re.search(r'Value\((.+)\)', goal_line)
                if general_match:
                    goal_expr = general_match.group(1).strip()
                    print(f"\nGeneral goal expression: {goal_expr}")

                    # Special handling for Sub expressions
                    if goal_expr.startswith("Sub(") and goal_expr.endswith(")"):
                        inner = goal_expr[4:-1]
                        parts = inner.split(',')
                        if len(parts) == 2:
                            expr1_str = parts[0].strip()
                            expr2_str = parts[1].strip()

                            # Handle angle measure subtraction
                            angle1_match = re.match(r'MeasureOfAngle\((\w+)\)', expr1_str)
                            angle2_match = re.match(r'MeasureOfAngle\((\w+)\)', expr2_str)
                            if angle1_match and angle2_match:
                                angle1_name = angle1_match.group(1)
                                angle2_name = angle2_match.group(1)

                                # Get angle variables
                                angle1_var = self.add_angle(angle1_name[0], angle1_name[1], angle1_name[2])
                                angle2_var = self.add_angle(angle2_name[0], angle2_name[1], angle2_name[2])

                                # Check the value constraint for the difference
                                diff_expr = angle1_var - angle2_var
                                success, value, status = self.check_value_constraint(diff_expr, model_answer_numeric)

                                if success:
                                    return True, ""
                                else:
                                    # Generate detailed feedback for angle subtraction
                                    detailed_feedback = self.generate_detailed_feedback(
                                        goal_type="general",
                                        goal_token=f"Sub({expr1_str},{expr2_str})",
                                        model_answer=model_answer_symbolic,
                                        verifier_expected_answer=value,
                                        status=status,
                                        additional_info=f"Angle 1: {angle1_name}\nAngle 2: {angle2_name}"
                                    )
                                    print(f"Detailed feedback generated for angle subtraction goal.")
                                    return False, detailed_feedback

                    # Special handling for single variables (most common case)
                    elif len(goal_expr) == 1 and goal_expr.isalpha() and goal_expr in self.variables:
                        # Get the Z3 variable directly
                        var = self.variables[goal_expr]

                        # Use the existing check_value_constraint function that handles multiple solutions
                        success, value, status = self.check_value_constraint(var, model_answer_numeric)

                        if success:
                            return True, ""
                        else:
                            # Generate detailed feedback with proper status
                            detailed_feedback = self.generate_detailed_feedback(
                                goal_type="general",
                                goal_token=goal_expr,
                                model_answer=model_answer_symbolic,
                                verifier_expected_answer=value,
                                status=status,
                                additional_info=f"Variable {goal_expr} is {'not uniquely determined' if status == 'multiple_values' else 'incompatible with expected value'}"
                            )
                            print(f"Detailed feedback generated for variable goal.")
                            return False, detailed_feedback

                    # For other general expressions, build a mapping for evaluation
                    if self.solver.check() == sat:
                        model = self.solver.model()

                        # Build mapping for variables and try to evaluate the expression
                        try:
                            # Build mapping for variables
                            mapping = {}
                            for var, z3var in self.variables.items():
                                try:
                                    val = model.eval(z3var, model_completion=True)
                                    val_str = str(val).replace('?', '')
                                    from fractions import Fraction
                                    mapping[var] = float(Fraction(val_str))
                                except Exception as e:
                                    print(f"Error converting free variable {var}: {e}")

                            # Add circle areas and triangle areas if needed
                            for circle, var in self.circle_areas.items():
                                value = model.eval(var)
                                value_str = str(value).replace('?', '')
                                try:
                                    from fractions import Fraction
                                    mapping[f"ac_{circle.lower()}"] = float(Fraction(value_str))
                                except Exception as e:
                                    print("Error converting circle area for", circle, ":", e)

                            for tri, var in self.triangle_areas.items():
                                value = model.eval(var)
                                value_str = str(value).replace('?', '')
                                try:
                                    from fractions import Fraction
                                    mapping[f"at_{tri.lower()}"] = float(Fraction(value_str))
                                except Exception as e:
                                    print("Error converting triangle area for", tri, ":", e)

                            # Evaluate the expression
                            verifier_expected_answer = self.evaluate_expression(goal_expr, mapping)

                            if abs(verifier_expected_answer - model_answer_numeric) < epsilon:
                                return True, ""
                            else:
                                # Generate detailed feedback for general expression
                                detailed_feedback = self.generate_detailed_feedback(
                                    goal_type="general",
                                    goal_token=goal_expr,
                                    model_answer=model_answer_symbolic,
                                    verifier_expected_answer=verifier_expected_answer,
                                    status="incompatible",
                                    additional_info=f"Evaluated expression: {goal_expr}\nComputed value: {verifier_expected_answer}\nExpected value: {model_answer_symbolic}"
                                )
                                print(f"Detailed feedback generated for general goal expression.")
                                return False, detailed_feedback
                        except Exception as e:
                            error_msg = f"Error evaluating general goal expression: {str(e)}"
                            print(f"Error evaluating general goal expression: {e}")
                            return False, error_msg
                    else:
                        # Generate detailed feedback for unsatisfiable
                        detailed_feedback = self.generate_detailed_feedback(
                            goal_type="general",
                            goal_token=goal_expr,
                            model_answer=model_answer_symbolic,
                            status="unsatisfiable"
                        )
                        print(f"Detailed feedback generated for general goal expression.")
                        return False, detailed_feedback

                feedback = "Error: Could not parse goal (not a recognized goal type)"
                print(
                    "Error: Could not parse goal (neither arc length, arc measure, angle, length, perimeter, nor general expression).")
                error = GeometricError(
                    tier=ErrorTier.TIER3_GOAL_NOT_REACHED,
                    message="Goal not recognized or not parsed properly",
                    details=f"Goal line content: {goal_line}"
                )
                print(f"\nError in {error.tier.name}: {error.message}")
                if error.details:
                    print("Details:", error.details)
                return False, feedback


            return True, ""
        except Exception as e:
            print(f"Error during proof verification: {str(e)}")
            import traceback
            traceback.print_exc()
            return False, f"Error during proof verification: {str(e)}"

    def collect_related_facts(self, goal_points, goal_type=None):
        """
        Collect only facts that directly involve the goal token and are meaningful for debugging
        Filters out trivial elements like individual points and basic angles
        """
        related_facts = {}
        goal_points_set = set(goal_points)
        goal_token = ''.join(goal_points)

        # 1. Check for perpendicular lines relevant to the goal
        perp_facts = []
        seen_perp_pairs = set()

        for pair in self.perpendicular_pairs:
            line1, line2 = pair

            # Check if at least one point from goal is in these lines
            if any(p in line1 for p in goal_points) or any(p in line2 for p in goal_points):
                # Create a normalized key to avoid duplicates
                key = tuple(sorted([line1, line2]))
                if key not in seen_perp_pairs:
                    seen_perp_pairs.add(key)
                    perp_facts.append(f"{line1} ⊥ {line2}")

        if perp_facts:
            related_facts["Perpendicular Lines"] = perp_facts

        # 2. Check for specific angle values in TEXT_CDL
        if goal_type == "angle":
            angle_values = []

            if hasattr(self, 'text_cdl_lines'):
                for line in self.text_cdl_lines:
                    # Look for direct values for this angle
                    angle_match = re.search(r'Equal\(MeasureOfAngle\(' + re.escape(goal_token) + r'\),(.+?)\)', line)
                    if angle_match:
                        value = angle_match.group(1).strip()
                        angle_values.append(f"∠{goal_token} = {value}")

            if angle_values:
                related_facts["Angle Values"] = angle_values

        # 3. Check for parallel lines involving goal points
        parallel_facts = []
        seen_parallel = set()

        for pair in self.parallel_pairs:
            line1, line2 = pair

            # Check if at least one point from goal is in these lines
            if any(p in line1 for p in goal_points) or any(p in line2 for p in goal_points):
                # Create a normalized key to avoid duplicates
                key = tuple(sorted([line1, line2]))
                if key not in seen_parallel:
                    seen_parallel.add(key)
                    parallel_facts.append(f"{line1} ∥ {line2}")

        if parallel_facts:
            related_facts["Parallel Lines"] = parallel_facts

        # 4. Check for special quadrilaterals
        # First, find relevant quadrilaterals that contain points from our goal
        special_quads = []
        seen_quads = set()

        for quad in self.polygons:
            if len(quad) == 4 and any(p in quad for p in goal_points):
                # Skip if we've already seen a cyclic variation of this quad
                normalized = min(quad[i:] + quad[:i] for i in range(len(quad)))
                if normalized in seen_quads:
                    continue
                seen_quads.add(normalized)

                properties = []
                # Check for various quadrilateral types
                if quad in self.parallelograms or any(
                        var in self.parallelograms for var in get_cyclic_variations(quad)):
                    properties.append("parallelogram")

                if hasattr(self, 'rectangles'):
                    if quad in self.rectangles or any(
                            var in self.rectangles for var in get_cyclic_variations_rectangle(quad)):
                        properties.append("rectangle")

                if hasattr(self, 'squares'):
                    if quad in self.squares or any(
                            var in self.squares for var in get_cyclic_variations_rectangle(quad)):
                        properties.append("square")

                if hasattr(self, 'rhombi'):
                    if quad in self.rhombi or any(var in self.rhombi for var in get_cyclic_variations_rectangle(quad)):
                        properties.append("rhombus")

                if properties:
                    special_quads.append(f"Quadrilateral {quad} ({', '.join(properties)})")

        if special_quads:
            related_facts["Special Quadrilaterals"] = special_quads

        # 5. Check for collinear facts involving goal points
        collinear_facts = []
        for collinear in self.collinear_facts:
            if any(p in collinear for p in goal_points) and len(collinear) >= 3:
                collinear_facts.append(f"Collinear {''.join(collinear)}")

        if collinear_facts:
            related_facts["Collinear Points"] = collinear_facts

        # 6. Check for special triangles
        special_triangles = []
        seen_triangles = set()

        for triangle in self.polygons:
            if len(triangle) == 3 and any(p in triangle for p in goal_points):
                # Skip if we've already seen a cyclic variation
                normalized = self.normalize_triangle(triangle)
                if normalized in seen_triangles:
                    continue
                seen_triangles.add(normalized)

                properties = []
                # Check for right triangle
                if triangle in self.right_triangles or normalized in self.right_triangles:
                    properties.append("right")

                # Check for isosceles
                if hasattr(self, 'isosceles_triangles'):
                    if triangle in self.isosceles_triangles or normalized in self.isosceles_triangles:
                        properties.append("isosceles")

                if properties:
                    special_triangles.append(f"Triangle {triangle} ({', '.join(properties)})")

        if special_triangles:
            related_facts["Special Triangles"] = special_triangles

        # Remove empty categories
        return {k: v for k, v in related_facts.items() if v}

    def find_related_theorems_for_variable(self, variable_name):
        """Find theorems that directly or indirectly constrain a variable goal."""
        related_theorems = []

        # First, identify all angle or length expressions defined in terms of the goal variable
        related_expressions = []
        related_angles = []
        related_lengths = []

        if hasattr(self, 'text_cdl_lines'):
            for line in self.text_cdl_lines:
                if variable_name in line:
                    # Look for angles defined in terms of goal_variable
                    angle_match = re.search(r'Equal\(MeasureOfAngle\((\w+)\),(.*?)\)', line)
                    if angle_match and variable_name in angle_match.group(2):
                        angle_token = angle_match.group(1)
                        related_expressions.append(f"MeasureOfAngle({angle_token})")
                        related_angles.append(angle_token)

                    # Look for lengths defined in terms of goal_variable
                    length_match = re.search(r'Equal\(LengthOfLine\((\w+)\),(.*?)\)', line)
                    if length_match and variable_name in length_match.group(2):
                        length_token = length_match.group(1)
                        related_expressions.append(f"LengthOfLine({length_token})")
                        related_lengths.append(length_token)

        # Now search for theorems that constrain these expressions
        for theorem_info in self.theorem_sequence:
            is_related = False

            # Check if goal variable is directly mentioned
            if variable_name in theorem_info["premise"] or any(variable_name in arg for arg in theorem_info["args"]):
                is_related = True

            # Check if any conclusion constrains a related expression
            if not is_related:
                for conclusion in theorem_info["conclusions"]:
                    # Check for direct mentions of related expressions
                    for expr in related_expressions:
                        if expr in conclusion:
                            is_related = True
                            break

                    # Also check for any angle tokens in the conclusion
                    for angle in related_angles:
                        if angle in conclusion:
                            is_related = True
                            break

                    if is_related:
                        break

            if is_related:
                related_theorems.append({
                    "step": theorem_info["step_number"],
                    "theorem": theorem_info["theorem_name"],
                    "args": theorem_info["args"],
                    "conclusion": ", ".join(theorem_info["conclusions"])
                })

        return related_theorems

    def find_related_theorems(self, goal_angle, goal_points):
        """Find only theorems that EXACTLY relate to the goal angle, with no false positives"""
        related_theorems = []
        goal_points_set = set(goal_points)

        for theorem_info in self.theorem_sequence:
            is_related = False

            # Check if goal angle is directly mentioned in conclusions
            for conclusion in theorem_info["conclusions"]:
                # Check for exact match
                if f"MeasureOfAngle({goal_angle})" in conclusion:
                    is_related = True
                    break

                # Check for possible normalizations of the angle
                # For a goal angle ABC, also check for CBA (normalized form)
                normalized_goal = self.normalize_angle_name(goal_angle)
                angle_matches = re.findall(r'MeasureOfAngle\((\w+)\)', conclusion)
                for angle in angle_matches:
                    normalized_angle = self.normalize_angle_name(angle)
                    if normalized_angle == normalized_goal:
                        is_related = True
                        break

            if is_related:
                related_theorems.append({
                    "step": theorem_info["step_number"],
                    "theorem": theorem_info["theorem_name"],
                    "args": theorem_info["args"],
                    "conclusion": ", ".join(theorem_info["conclusions"])
                })

        return related_theorems

    def add_all_side_ratios_for_similar_triangles(self, tri1: str, tri2: str):
        # 1) Get the 3 vertices in order, e.g. tri1='BAE', tri2='CAD'
        def get_triangle_vertices(triangle_name: str) -> list:
            return list(triangle_name)

        verts1 = get_triangle_vertices(tri1)
        verts2 = get_triangle_vertices(tri2)

        # 2) Normalize the triangles and form a key
        norm_tris = self.normalize_similar_triangles(tri1, tri2)
        if not norm_tris:
            return  # Invalid triangles, do nothing

        # If we have already added constraints for this pair, return immediately.
        if norm_tris in self.added_ratio_constraints:
            return

        # Ensure a ratio variable exists:
        if norm_tris not in self.triangle_ratios:
            var_name = f"ratio_{norm_tris[0]}_{norm_tris[1]}"
            self.triangle_ratios[norm_tris] = Real(var_name)
        ratio = self.triangle_ratios[norm_tris]

        # 3) Add constraints for each corresponding side pair.
        for i in range(3):
            j = (i + 1) % 3
            p1a, p1b = verts1[i], verts1[j]
            p2a, p2b = verts2[i], verts2[j]
            side1_var = self.add_length(p1a, p1b)
            side2_var = self.add_length(p2a, p2b)
            self.solver.add(side1_var == side2_var * ratio)

        # Flag that we have now added the ratio constraints for this triangle pair.
        self.added_ratio_constraints.add(norm_tris)

    def contains_algebraic_variables(self, expr: str) -> bool:
        """Check if an expression contains algebraic variables (letters that aren't part of math functions)."""
        import re

        # First remove all numbers from the expression
        expr_without_nums = re.sub(r'\d+(\.\d+)?', '', expr)

        # Remove operators and parentheses
        expr_clean = re.sub(r'[+\-*/()^]', '', expr_without_nums)

        # Remove known math constants and functions
        math_terms = ['pi', 'sqrt', 'sin', 'cos', 'tan', 'log', 'ln', 'exp']
        for term in math_terms:
            expr_clean = expr_clean.lower().replace(term, '')

        # If any letters remain, it contains algebraic variables
        return bool(re.search(r'[a-zA-Z]', expr_clean))


    def add_algebraic_length(self, line_name: str, expression: str):
        """
        Add a length constraint given an algebraic expression.
        For instance, for a TEXT_CDL line like
          Equal(LengthOfLine(JM),5)
        or
          Equal(LengthOfLine(LJ),y)
        this function will create a Z3 variable for the segment (using add_length)
        and then add the equality constraint. It also handles algebraic expressions.
        """
        print(f"\nAdding algebraic length constraint: {line_name} = {expression}")

        # First try to parse the expression as a numeric value.
        try:
            value = float(expression)
            print(f"Adding numeric value for {line_name}: {value}")
            # Use add_length to get the variable (which normalizes the name)
            length_var = self.add_length(line_name[0], line_name[1])
            self.solver.add(length_var == value)
            print(f"Stored numeric value: {line_name} = {value}")
            return
        except ValueError:
            # Not a pure number, so proceed as an algebraic expression.
            pass

        # Extract free variable names from the expression.
        variables = self.extract_variables(expression)
        for var in variables:
            if var not in self.variables:
                self.variables[var] = Real(var)
                print(f"Created new variable for algebraic length: {var}")

        # Get (or create) the length variable using your normalization.
        length_var = self.add_length(line_name[0], line_name[1])
        # Parse the expression into a Z3 expression.
        expr = self.parse_algebraic_expression(expression)
        self.solver.add(length_var == expr)
        print(f"Added constraint: {line_name} == {expr}")

    def check_length_equality(self, line1: str, line2: str) -> bool:
        # Get (or create) the Z3 variables for each segment.
        var1 = self.add_length(line1[0], line1[1])
        var2 = self.add_length(line2[0], line2[1])
        temp_solver = Solver()
        for c in self.solver.assertions():
            temp_solver.add(c)
        # If adding the inequality makes the system unsat, then they are equal.
        temp_solver.add(var1 != var2)
        return temp_solver.check() == unsat

    def apply_trig_constraints(self):
        """
        Applies numeric constraints to sine and cosine variables
        when the corresponding angles have unique values.
        """
        import math
        from z3 import sat, unsat, Solver, Or

        # First, check if the solver is satisfiable
        if self.solver.check() != sat:
            print("Solver is unsatisfiable, cannot apply trig constraints")
            return 0

        # Get the current model
        model = self.solver.model()

        # Look for all sin_XXX and cos_XXX variables in self.variables
        trig_vars = []

        for var_name, var in self.variables.items():
            if var_name.startswith("sin_") or var_name.startswith("cos_"):
                parts = var_name.split("_", 1)
                if len(parts) == 2:
                    func, angle_name = parts
                    angle_var_name = f"angle_{angle_name}"

                    if angle_var_name in self.angles:
                        trig_vars.append({
                            "trig_var_name": var_name,
                            "angle_var_name": angle_var_name,
                            "angle_var": self.angles[angle_var_name],
                            "trig_var": self.variables[var_name],
                            "func": func,
                            "angle_name": angle_name
                        })

        if not trig_vars:
            return 0

        # For each trig variable, check if the angle has a unique value
        constraints_added = 0

        for data in trig_vars:
            angle_var = data["angle_var"]
            trig_var = data["trig_var"]
            func = data["func"]
            angle_name = data["angle_name"]
            trig_var_name = data["trig_var_name"]

            # Try to get the current angle value from the model
            try:
                angle_val_str = model.eval(angle_var).as_decimal(10)
                if angle_val_str.endswith('?'):
                    angle_val_str = angle_val_str[:-1]
                angle_val = float(angle_val_str)

                # Check if this angle value is uniquely determined
                temp_solver = Solver()
                for c in self.solver.assertions():
                    temp_solver.add(c)

                epsilon = 1e-6
                temp_solver.add(Or(
                    angle_var < angle_val - epsilon,
                    angle_var > angle_val + epsilon
                ))

                if temp_solver.check() == unsat:
                    # Calculate exact trig value based on special cases or general formula
                    if abs(angle_val - 90) < epsilon:
                        # 90 degrees
                        if func == "sin":
                            exact_trig_val = 1.0
                        else:  # cos
                            exact_trig_val = 0.0
                    elif abs(angle_val - 0) < epsilon:
                        # 0 degrees
                        if func == "sin":
                            exact_trig_val = 0.0
                        else:  # cos
                            exact_trig_val = 1.0
                    elif abs(angle_val - 180) < epsilon:
                        # 180 degrees
                        if func == "sin":
                            exact_trig_val = 0.0
                        else:  # cos
                            exact_trig_val = -1.0
                    elif abs(angle_val - 45) < epsilon or abs(angle_val - 135) < epsilon:
                        # 45 or 135 degrees
                        sqrt2_over_2 = math.sqrt(2) / 2
                        if func == "sin":
                            exact_trig_val = sqrt2_over_2
                        else:  # cos
                            exact_trig_val = sqrt2_over_2 if abs(angle_val - 45) < epsilon else -sqrt2_over_2
                    elif abs(angle_val - 30) < epsilon or abs(angle_val - 150) < epsilon:
                        # 30 or 150 degrees
                        if func == "sin":
                            exact_trig_val = 0.5
                        else:  # cos
                            exact_trig_val = math.sqrt(3) / 2 if abs(angle_val - 30) < epsilon else -math.sqrt(3) / 2
                    elif abs(angle_val - 60) < epsilon or abs(angle_val - 120) < epsilon:
                        # 60 or 120 degrees
                        if func == "sin":
                            exact_trig_val = math.sqrt(3) / 2
                        else:  # cos
                            exact_trig_val = 0.5 if abs(angle_val - 60) < epsilon else -0.5
                    else:
                        # General case
                        if func == "sin":
                            exact_trig_val = math.sin(math.radians(angle_val))
                        else:  # cos
                            exact_trig_val = math.cos(math.radians(angle_val))

                    # Round to help with numerical stability
                    exact_trig_val = round(exact_trig_val, 10)

                    # Check if the trig variable is already constrained to this value
                    trig_temp_solver = Solver()
                    for c in self.solver.assertions():
                        trig_temp_solver.add(c)

                    trig_temp_solver.add(Or(
                        trig_var < exact_trig_val - epsilon,
                        trig_var > exact_trig_val + epsilon
                    ))

                    if trig_temp_solver.check() == sat:
                        # Trig variable can have a different value, add constraint
                        self.solver.add(trig_var == exact_trig_val)
                        constraints_added += 1
                        print(f"Added constraint: {func}({angle_name}) = {exact_trig_val} (angle = {angle_val}°)")

            except Exception as e:
                print(f"Error processing angle {angle_name}: {e}")

        return constraints_added



    def adding_conclution(self, theorem_name: str, args: List[str], premise: str, conclusions: List[str]) -> \
            Optional[GeometricError]:
        print(f"\nProcessing theorem step: {theorem_name}")
        print(f"Arguments: {args}")
        print(f"Premise: '{premise}'")
        print(f"Conclusions: {conclusions}")

        valid_theorems = [
            "parallelogram_property_opposite_angle_equal",
            "adjacent_complementary_angle",
            "parallel_property_alternate_interior_angle",
            "parallel_property_corresponding_angle",
            "angle_addition",
            "quadrilateral_property_angle_sum",
            "line_addition",
            "right_triangle_judgment_angle",
            "right_triangle_property_pythagorean",
            "similar_triangle_property_line_ratio",
            "similar_triangle_judgment_aa",
            "triangle_perimeter_formula",
            "triangle_property_angle_sum",
            "diameter_of_circle_property_right_angle",
            "triangle_area_formula_sine",
            "diameter_of_circle_property_length_equal",
            "circle_property_length_of_radius_and_diameter",
            "circle_area_formula",
            "mirror_similar_triangle_judgment_aa",
            "mirror_similar_triangle_property_line_ratio",
            "sine_theorem",
            "tangent_of_circle_property_perpendicular",
            "arc_property_center_angle",
            "arc_property_circumference_angle_external",
            "circle_property_circular_power_segment_and_segment_angle",
            "arc_length_formula",
            "arc_property_circumference_angle_internal",
            "parallel_property_ipsilateral_internal_angle",
            "parallel_property_collinear_extend",
            "midsegment_of_triangle_judgment_parallel",
            "circle_property_chord_perpendicular_bisect_chord",
            "radius_of_circle_property_length_equal",
            "circle_property_circular_power_tangent_and_segment_line",
            "circle_property_circular_power_segment_and_segment_line",
            "rectangle_property_diagonal_equal",
            "parallelogram_property_diagonal_bisection",
            "isosceles_triangle_judgment_line_equal",
            "isosceles_triangle_property_angle_equal",
            "altitude_of_quadrilateral_judgment_left_vertex",
            "parallelogram_property_opposite_line_equal",
            "parallelogram_area_formula_common",
            "altitude_of_quadrilateral_judgment_diagonal",
            "perpendicular_bisector_judgment_distance_equal",
            "cosine_theorem",
            "circle_property_circular_power_chord_and_chord",
            "round_angle",
            "flat_angle",
            "altitude_of_triangle_judgment",
            "triangle_area_formula_common",
            "perpendicular_bisector_property_distance_equal",
            "parallelogram_judgment_parallel_and_parallel",
            "vertical_angle",
            "isosceles_triangle_judgment_angle_equal",
            "incenter_of_triangle_judgment_intersection",
            "median_of_triangle_judgment",
            "right_triangle_property_length_of_median",
            "congruent_triangle_property_line_equal",
            "congruent_triangle_property_angle_equal",
            "mirror_congruent_triangle_judgment_aas",
            "mirror_congruent_triangle_property_line_equal",
            "midsegment_of_triangle_judgment_midpoint",
            "midsegment_of_triangle_property_length",
            "parallel_judgment_par_par",
            "mirror_congruent_triangle_judgment_sas",
            "mirror_congruent_triangle_property_angle_equal",
            "arc_addition_measure",
            "diameter_of_circle_judgment_pass_centre",
            "isosceles_triangle_property_line_coincidence",
            "parallelogram_area_formula_sine",
            "midsegment_of_quadrilateral_property_length",
            "tangent_of_circle_property_length_equal",
            "quadrilateral_perimeter_formula",
            "congruent_triangle_judgment_aas",
            "similar_triangle_property_area_square_ratio",
            "congruent_arc_judgment_chord_equal",
            "congruent_arc_property_measure_equal",
            "equilateral_triangle_property_angle",
            "round_arc",
            "perpendicular_judgment_angle",
            "rectangle_judgment_right_angle",
            "circle_property_angle_of_osculation",
            "bisector_of_angle_judgment_angle_equal",
            "bisector_of_angle_property_line_ratio",
            "diameter_of_circle_judgment_right_angle"
        ]

        if theorem_name not in valid_theorems:
            return GeometricError(
                tier=ErrorTier.TIER1_THEOREM_CALL_SYNTAX_VIOLATION,
                message=f"Unknown theorem: {theorem_name}",
                details=f"Valid theorems are: {valid_theorems}"
            )

        if theorem_name == "parallelogram_property_opposite_angle_equal":
            version = args[0]
            if version == "1":
                angles_match = re.search(r'Equal\(MeasureOfAngle\((\w+)\),\s*MeasureOfAngle\((\w+)\)\)', conclusions[0])
                if angles_match:
                    angle1, angle2 = angles_match.group(1), angles_match.group(2)

                    # Add both angles to solver
                    angle1_var = self.add_angle(angle1[0], angle1[1], angle1[2])
                    angle2_var = self.add_angle(angle2[0], angle2[1], angle2[2])
                    self.solver.add(angle1_var == angle2_var)
                    print(f"Added parallelogram opposite angle equality: {angle1} = {angle2}")

        elif theorem_name == "bisector_of_angle_judgment_angle_equal":
            version = args[0]
            if version == "1":
                # Parse the conclusion to get the bisector and angle
                match = re.search(r'IsBisectorOfAngle\((\w+),(\w+)\)', conclusions[0])
                if not match:
                    return GeometricError(
                        tier=ErrorTier.TIER1_THEOREM_CALL_SYNTAX_VIOLATION,
                        message="Conclusion format error for bisector_of_angle_judgment_angle_equal",
                        details=f"Expected IsBisectorOfAngle(...) pattern but got {conclusions[0]}"
                    )

                bisector, angle_name = match.groups()  # e.g., "BD", "ABC"

                # Initialize angle_bisectors if it doesn't exist
                if not hasattr(self, "angle_bisectors"):
                    self.angle_bisectors = []

                # Add the angle bisector information
                self.angle_bisectors.append((bisector, angle_name))

                # Extract the key points
                vertex = angle_name[1]  # Middle letter is the vertex
                left_arm = angle_name[0]  # First letter of the original angle
                right_arm = angle_name[2]  # Last letter of the original angle
                bisector_point = bisector[1]  # Second letter of the bisector

                # Define the two sub-angles
                left_subangle = left_arm + vertex + bisector_point  # e.g., "ABD"
                right_subangle = bisector_point + vertex + right_arm  # e.g., "DBC"

                # Create angle variables for both sub-angles
                left_angle_var = self.add_angle(left_subangle[0], left_subangle[1], left_subangle[2])
                right_angle_var = self.add_angle(right_subangle[0], right_subangle[1], right_subangle[2])

                # Add the constraint that both angles are equal (definition of angle bisector)
                self.solver.add(left_angle_var == right_angle_var)

                print(f"Added angle bisector: {bisector} is a bisector of angle {angle_name}")
                print(f"Added constraint: angle {left_subangle} = angle {right_subangle}")
                return None
            else:
                return GeometricError(
                    tier=ErrorTier.TIER1_THEOREM_CALL_SYNTAX_VIOLATION,
                    message=f"Unsupported version {version} for bisector_of_angle_judgment_angle_equal",
                    details="Only version 1 is supported"
                )
        elif theorem_name == "circle_property_angle_of_osculation":
            version = args[0]
            if version in {"1", "2"}:
                # Parse the conclusion to extract the angle and arc
                match = re.search(
                    r'Equal\(MeasureOfAngle\((\w{3})\),Mul\(MeasureOfArc\((\w+)\),([\d/\.]+)\)\)',
                    conclusions[0]
                )

                if not match:
                    return GeometricError(
                        tier=ErrorTier.TIER1_THEOREM_CALL_SYNTAX_VIOLATION,
                        message="Conclusion format error for circle_property_angle_of_osculation",
                        details=f"Expected Equal(MeasureOfAngle(...),Mul(MeasureOfArc(...),factor)) pattern but got {conclusions[0]}"
                    )

                angle_str, arc_str, factor_str = match.groups()

                # Verify angle matches the expected angle based on version
                if version == "1":
                    arc = args[1].strip()  # "OAB"
                    point = args[2].strip()  # "P"
                    expected_angle = arc[2] + arc[1] + point  # "BAP"

                    if angle_str != expected_angle:
                        return GeometricError(
                            tier=ErrorTier.TIER1_THEOREM_CALL_SYNTAX_VIOLATION,
                            message=f"Angle in conclusion ({angle_str}) doesn't match expected angle ({expected_angle})",
                            details="The angle must match the theorem version's expected pattern"
                        )
                else:  # version == "2"
                    arc = args[1].strip()  # "OAB"
                    point = args[2].strip()  # "P"
                    expected_angle = point + arc[2] + arc[1]  # "PBA"

                    if angle_str != expected_angle:
                        return GeometricError(
                            tier=ErrorTier.TIER1_THEOREM_CALL_SYNTAX_VIOLATION,
                            message=f"Angle in conclusion ({angle_str}) doesn't match expected angle ({expected_angle})",
                            details="The angle must match the theorem version's expected pattern"
                        )

                # Get angle variable
                angle_var = self.add_angle(angle_str[0], angle_str[1], angle_str[2])

                # Get arc variable
                arc_var = self.add_arc(arc_str)

                # Parse the factor (should be 1/2)
                try:
                    from fractions import Fraction
                    factor_val = float(Fraction(factor_str))
                except Exception as e:
                    print(f"Error parsing factor {factor_str}: {e}, defaulting to 0.5")
                    factor_val = 0.5

                # Add the constraint: angle = factor * arc
                self.solver.add(angle_var == factor_val * arc_var)

                print(
                    f"Added angle of osculation constraint: MeasureOfAngle({angle_str}) = {factor_val} * MeasureOfArc({arc_str})")
                return None
            else:
                return GeometricError(
                    tier=ErrorTier.TIER1_THEOREM_CALL_SYNTAX_VIOLATION,
                    message=f"Unsupported version {version} for circle_property_angle_of_osculation",
                    details="Supported versions are 1 and 2"
                )

        elif theorem_name == "bisector_of_angle_property_line_ratio":
            version = args[0]
            if version == "1":
                # Parse the conclusion: Equal(Mul(LengthOfLine(CD),LengthOfLine(BA)),Mul(LengthOfLine(DA),LengthOfLine(BC)))
                ratio_match = re.search(
                    r'Equal\(Mul\(LengthOfLine\((\w{2})\),LengthOfLine\((\w{2})\)\),Mul\(LengthOfLine\((\w{2})\),LengthOfLine\((\w{2})\)\)\)',
                    conclusions[0]
                )

                if not ratio_match:
                    return GeometricError(
                        tier=ErrorTier.TIER1_THEOREM_CALL_SYNTAX_VIOLATION,
                        message="Conclusion format error for bisector_of_angle_property_line_ratio",
                        details=f"Expected length ratio pattern not found in: {conclusions[0]}"
                    )

                segment1, segment2, segment3, segment4 = ratio_match.groups()

                # Create length variables for all segments
                len1 = self.add_length(segment1[0], segment1[1])
                len2 = self.add_length(segment2[0], segment2[1])
                len3 = self.add_length(segment3[0], segment3[1])
                len4 = self.add_length(segment4[0], segment4[1])

                # Add the constraint: len1 * len2 = len3 * len4
                self.solver.add(len1 * len2 == len3 * len4)

                print(f"Added angle bisector ratio constraint: {segment1} * {segment2} = {segment3} * {segment4}")
                return None
            else:
                return GeometricError(
                    tier=ErrorTier.TIER1_THEOREM_CALL_SYNTAX_VIOLATION,
                    message=f"Unsupported version {version} for bisector_of_angle_property_line_ratio",
                    details="Only version 1 is supported"
                )


        elif theorem_name == "diameter_of_circle_judgment_right_angle":
            version = args[0]
            if version == "1":
                if len(args) < 3:
                    return GeometricError(
                        tier=ErrorTier.TIER1_THEOREM_CALL_SYNTAX_VIOLATION,
                        message="Insufficient arguments for diameter_of_circle_judgment_right_angle",
                        details="Expected: diameter_of_circle_judgment_right_angle(1, angle, circle)"
                    )

                angle_token = args[1].strip()  # e.g., "BCA"
                circle_token = args[2].strip()  # e.g., "O"

                # Parse the conclusion to extract the diameter line
                diameter_match = re.search(r'IsDiameterOfCircle\((\w+),(\w+)\)', conclusions[0])
                if not diameter_match:
                    return GeometricError(
                        tier=ErrorTier.TIER1_THEOREM_CALL_SYNTAX_VIOLATION,
                        message="Conclusion format error for diameter_of_circle_judgment_right_angle",
                        details=f"Expected IsDiameterOfCircle(...) pattern but got {conclusions[0]}"
                    )

                diameter_line, conclusion_circle = diameter_match.groups()

                # Verify the circle in the conclusion matches the one in the arguments
                if conclusion_circle != circle_token:
                    return GeometricError(
                        tier=ErrorTier.TIER1_THEOREM_CALL_SYNTAX_VIOLATION,
                        message=f"Circle mismatch: argument has {circle_token} but conclusion has {conclusion_circle}",
                        details="The circle in the conclusion must match the one in the arguments"
                    )

                # Extract the endpoints of the diameter (the non-vertex points of the angle)
                # For angle BCA, the diameter is AB
                vertex = angle_token[1]  # Middle letter is the vertex (e.g., "C")
                endpoints = [p for p in angle_token if p != vertex]  # e.g., ["B", "A"]
                expected_diameter = ''.join(endpoints)  # e.g., "BA"

                # Check if the diameter in the conclusion matches the expected one (considering both orders)
                if diameter_line != expected_diameter and diameter_line != expected_diameter[::-1]:
                    return GeometricError(
                        tier=ErrorTier.TIER1_THEOREM_CALL_SYNTAX_VIOLATION,
                        message=f"Diameter mismatch: expected {expected_diameter} or {expected_diameter[::-1]} but got {diameter_line}",
                        details="The diameter in the conclusion must connect the non-vertex points of the angle"
                    )

                # Record the diameter fact
                if not hasattr(self, "is_diameter_of_circle"):
                    self.is_diameter_of_circle = []

                # Add both the original and reversed diameter lines
                if (diameter_line, circle_token) not in self.is_diameter_of_circle:
                    self.is_diameter_of_circle.append((diameter_line, circle_token))

                if (diameter_line[::-1], circle_token) not in self.is_diameter_of_circle:
                    self.is_diameter_of_circle.append((diameter_line[::-1], circle_token))

                # If you have diameter and radius variables, establish the relationship
                if hasattr(self, "circle_radii") and hasattr(self, "circle_diameters"):
                    if circle_token in self.circle_radii:
                        # Create diameter variable if it doesn't exist
                        diam_name = f"diameter_{circle_token}"
                        if diam_name not in self.circle_diameters:
                            self.circle_diameters[diam_name] = Real(diam_name)
                            self.solver.add(self.circle_diameters[diam_name] >= 0)

                        # Create length variable for the diameter
                        diam_length = self.add_length(diameter_line[0], diameter_line[1])

                        # Set diameter length = diameter variable
                        self.solver.add(diam_length == self.circle_diameters[diam_name])

                        # Set diameter = 2 * radius
                        radius_var = self.circle_radii[circle_token]
                        self.solver.add(self.circle_diameters[diam_name] == 2 * radius_var)

                print(
                    f"Added diameter fact: {diameter_line} is a diameter of circle {circle_token} (by right angle inscribed in semicircle)")
                return None
            else:
                return GeometricError(
                    tier=ErrorTier.TIER1_THEOREM_CALL_SYNTAX_VIOLATION,
                    message=f"Unsupported version {version} for diameter_of_circle_judgment_right_angle",
                    details="Only version 1 is supported"
                )


        elif theorem_name == "rectangle_judgment_right_angle":
            version = args[0]
            if version == "1":
                # Parse the conclusion to extract the rectangle name
                rectangle_match = re.search(r'Rectangle\((\w+)\)', conclusions[0])
                if not rectangle_match:
                    return GeometricError(
                        tier=ErrorTier.TIER1_THEOREM_CALL_SYNTAX_VIOLATION,
                        message="Conclusion format error for rectangle_judgment_right_angle",
                        details=f"Expected Rectangle(...) pattern but got {conclusions[0]}"
                    )

                quad = rectangle_match.group(1)  # e.g., "ABCD"

                # Create or get the rectangles collection
                if not hasattr(self, "rectangles"):
                    self.rectangles = set()

                # Add all cyclic variations of the quadrilateral to the rectangles set
                quad_variations = get_cyclic_variations(quad)
                self.rectangles.update(quad_variations)

                # Since a rectangle has all right angles, add constraints for all four angles
                for i in range(4):
                    angle_name = quad[i] + quad[(i + 1) % 4] + quad[(i + 2) % 4]  # e.g., "ABC"
                    angle_var = self.add_angle(angle_name[0], angle_name[1], angle_name[2])
                    self.solver.add(angle_var == 90)
                    print(f"Added right angle constraint: angle {angle_name} = 90°")

                print(f"Added rectangle: {quad}")
                return None
            else:
                return GeometricError(
                    tier=ErrorTier.TIER1_THEOREM_CALL_SYNTAX_VIOLATION,
                    message=f"Unsupported version {version} for rectangle_judgment_right_angle",
                    details="Only version 1 is supported"
                )

        elif theorem_name == "perpendicular_judgment_angle":
            version = args[0]
            if version == "1":
                # Extract the two perpendicular lines from the conclusion
                perpendicular_match = re.search(r'PerpendicularBetweenLine\((\w+),(\w+)\)', conclusions[0])
                if not perpendicular_match:
                    return GeometricError(
                        tier=ErrorTier.TIER1_THEOREM_CALL_SYNTAX_VIOLATION,
                        message="Conclusion format error for perpendicular_judgment_angle",
                        details=f"Expected PerpendicularBetweenLine(...) pattern but got {conclusions[0]}"
                    )

                line1, line2 = perpendicular_match.groups()

                # Initialize the perpendicular_pairs set if it doesn't exist
                if not hasattr(self, "perpendicular_pairs"):
                    self.perpendicular_pairs = set()

                # Add both directions to the perpendicular pairs
                self.perpendicular_pairs.add((line1, line2))
                self.perpendicular_pairs.add((line2, line1))

                # Also add reversed line representations
                self.perpendicular_pairs.add((line1[::-1], line2))
                self.perpendicular_pairs.add((line2, line1[::-1]))
                self.perpendicular_pairs.add((line1, line2[::-1]))
                self.perpendicular_pairs.add((line2[::-1], line1))
                self.perpendicular_pairs.add((line1[::-1], line2[::-1]))
                self.perpendicular_pairs.add((line2[::-1], line1[::-1]))

                # Find the shared point between the lines
                shared_point = None
                for p in line1:
                    if p in line2:
                        shared_point = p
                        break

                if shared_point is not None:
                    # Construct the angle formed by these lines
                    other_point1 = next(p for p in line1 if p != shared_point)
                    other_point2 = next(p for p in line2 if p != shared_point)
                    angle_name = other_point1 + shared_point + other_point2

                    # Add the 90-degree constraint to this angle
                    angle_var = self.add_angle(angle_name[0], angle_name[1], angle_name[2])
                    self.solver.add(angle_var == 90)
                    print(f"Added perpendicular constraint: angle {angle_name} = 90°")

                print(f"Added perpendicular relationship: {line1} ⊥ {line2}")
                return None
            else:
                return GeometricError(
                    tier=ErrorTier.TIER1_THEOREM_CALL_SYNTAX_VIOLATION,
                    message=f"Unsupported version {version} for perpendicular_judgment_angle",
                    details="Only version 1 is supported"
                )
        elif theorem_name == "round_arc":
            version = args[0]
            if version == "1":
                # Parse the conclusion to extract the arcs
                match = re.search(r'Equal\(Add\(MeasureOfArc\((\w+)\),MeasureOfArc\((\w+)\)\),360\)', conclusions[0])
                if not match:
                    return GeometricError(
                        tier=ErrorTier.TIER1_THEOREM_CALL_SYNTAX_VIOLATION,
                        message="Conclusion format error for round_arc",
                        details=f"Expected Equal(Add(MeasureOfArc(...),MeasureOfArc(...)),360) pattern but got {conclusions[0]}"
                    )

                arc1, arc2 = match.groups()

                # Get or create arc measure variables
                arc1_var = self.add_arc(arc1)
                arc2_var = self.add_arc(arc2)

                # Add the constraint that the sum of arc measures equals 360 degrees
                self.solver.add(arc1_var + arc2_var == 360)

                print(f"Added round arc constraint: MeasureOfArc({arc1}) + MeasureOfArc({arc2}) = 360°")
                return None
            else:
                return GeometricError(
                    tier=ErrorTier.TIER1_THEOREM_CALL_SYNTAX_VIOLATION,
                    message=f"Unsupported version {version} for round_arc",
                    details="Only version 1 is supported"
                )

        # For the tangent_of_circle_property_length_equal theorem
        elif theorem_name == "tangent_of_circle_property_length_equal":
            version = args[0]
            if version == "1":
                # Extract the two tangent lines and the circle from the args
                line1 = args[1].strip()  # e.g., "AM"
                line2 = args[2].strip()  # e.g., "AG"
                circle = args[3].strip()  # e.g., "O"

                # Check conclusion format
                match = re.search(r'Equal\(LengthOfLine\((\w+)\),LengthOfLine\((\w+)\)\)', conclusions[0])
                if match:
                    # Get length variables for both tangent lines
                    len1_var = self.add_length(line1[0], line1[1])
                    len2_var = self.add_length(line2[0], line2[1])

                    # Add the constraint that they are equal
                    self.solver.add(len1_var == len2_var)

                    print(f"Added tangent length equality constraint: {line1} = {line2}")
                    return None
                else:
                    return GeometricError(
                        tier=ErrorTier.TIER1_THEOREM_CALL_SYNTAX_VIOLATION,
                        message="Conclusion format error for tangent_of_circle_property_length_equal",
                        details=f"Expected Equal(LengthOfLine(XX),LengthOfLine(YY)) but got {conclusions[0]}"
                    )
            else:
                return GeometricError(
                    tier=ErrorTier.TIER1_THEOREM_CALL_SYNTAX_VIOLATION,
                    message=f"Unsupported version {version} for tangent_of_circle_property_length_equal"
                )


        elif theorem_name == "congruent_arc_judgment_chord_equal":
            version = args[0]
            if version == "1":
                # Parse the conclusion to extract the two arcs
                arc_match = re.search(r'CongruentBetweenArc\((\w+),(\w+)\)', conclusions[0])
                if not arc_match:
                    return GeometricError(
                        tier=ErrorTier.TIER1_THEOREM_CALL_SYNTAX_VIOLATION,
                        message="Conclusion format error for congruent_arc_judgment_chord_equal",
                        details=f"Expected CongruentBetweenArc(...) pattern but got {conclusions[0]}"
                    )

                arc1, arc2 = arc_match.groups()

                # Store the congruent arc relationship
                if not hasattr(self, "congruent_arcs"):
                    self.congruent_arcs = []

                # Create a canonical representation of the arc pair to avoid duplicates
                canonical_arc_pair = tuple(sorted([arc1, arc2]))

                if canonical_arc_pair not in self.congruent_arcs:
                    self.congruent_arcs.append(canonical_arc_pair)

                print(f"Added congruent arcs relationship: {arc1} and {arc2} are congruent")
                return None
            else:
                return GeometricError(
                    tier=ErrorTier.TIER1_THEOREM_CALL_SYNTAX_VIOLATION,
                    message=f"Unsupported version {version} for congruent_arc_judgment_chord_equal",
                    details="Only version 1 is supported"
                )

        elif theorem_name == "congruent_arc_property_measure_equal":
            version = args[0]
            if version == "1":
                # Parse the conclusion to extract the arc measures
                match = re.search(r'Equal\(MeasureOfArc\((\w+)\),MeasureOfArc\((\w+)\)\)', conclusions[0])
                if not match:
                    return GeometricError(
                        tier=ErrorTier.TIER1_THEOREM_CALL_SYNTAX_VIOLATION,
                        message="Conclusion format error for congruent_arc_property_measure_equal",
                        details=f"Expected Equal(MeasureOfArc(...),MeasureOfArc(...)) pattern but got {conclusions[0]}"
                    )

                arc1, arc2 = match.groups()

                # Get or create arc measure variables
                arc1_var = self.add_arc(arc1)
                arc2_var = self.add_arc(arc2)

                # Add the constraint that the arc measures are equal
                self.solver.add(arc1_var == arc2_var)

                print(f"Added arc measure equality: MeasureOfArc({arc1}) = MeasureOfArc({arc2})")
                return None
            else:
                return GeometricError(
                    tier=ErrorTier.TIER1_THEOREM_CALL_SYNTAX_VIOLATION,
                    message=f"Unsupported version {version} for congruent_arc_property_measure_equal",
                    details="Only version 1 is supported"
                )


        elif theorem_name == "equilateral_triangle_property_angle":
            version = args[0]
            if version == "1":
                # Parse the conclusion to extract the angle
                match = re.search(r'Equal\(MeasureOfAngle\((\w{3})\),60\)', conclusions[0])
                if not match:
                    return GeometricError(
                        tier=ErrorTier.TIER1_THEOREM_CALL_SYNTAX_VIOLATION,
                        message="Conclusion format error for equilateral_triangle_property_angle",
                        details=f"Expected Equal(MeasureOfAngle(...),60) pattern but got {conclusions[0]}"
                    )

                angle = match.group(1)  # e.g., "CAB"

                # Set the angle to 60 degrees
                angle_var = self.add_angle(angle[0], angle[1], angle[2])
                self.solver.add(angle_var == 60)

                # For equilateral triangles, all angles are equal to 60 degrees
                # Let's set all angles in the triangle to 60 degrees
                triangle = args[1].strip()  # e.g., "ABC"

                # Get all angles in the triangle
                angles = [
                    triangle[0] + triangle[1] + triangle[2],  # e.g., "ABC"
                    triangle[1] + triangle[2] + triangle[0],  # e.g., "BCA"
                    triangle[2] + triangle[0] + triangle[1]  # e.g., "CAB"
                ]

                # Set all angles to 60 degrees
                for tri_angle in angles:
                    tri_angle_var = self.add_angle(tri_angle[0], tri_angle[1], tri_angle[2])
                    self.solver.add(tri_angle_var == 60)
                    print(f"Set angle in equilateral triangle: MeasureOfAngle({tri_angle}) = 60°")

                return None
            else:
                return GeometricError(
                    tier=ErrorTier.TIER1_THEOREM_CALL_SYNTAX_VIOLATION,
                    message=f"Unsupported version {version} for equilateral_triangle_property_angle",
                    details="Only version 1 is supported"
                )


        elif theorem_name == "similar_triangle_property_area_square_ratio":
            version = args[0]
            if version == "1":
                # Parse conclusion to extract triangle names
                area_ratio_match = re.search(
                    r'Equal\(AreaOfTriangle\((\w+)\),Mul\(AreaOfTriangle\((\w+)\),RatioOfSimilarTriangle\((\w+),(\w+)\),RatioOfSimilarTriangle\((\w+),(\w+)\)\)\)',
                    conclusions[0]
                )

                if not area_ratio_match:
                    return GeometricError(
                        tier=ErrorTier.TIER1_THEOREM_CALL_SYNTAX_VIOLATION,
                        message="Conclusion format error for similar_triangle_property_area_square_ratio",
                        details=f"Expected area ratio pattern not found in: {conclusions[0]}"
                    )

                tri1, tri2, ratio_tri1_1, ratio_tri2_1, ratio_tri1_2, ratio_tri2_2 = area_ratio_match.groups()

                # Verify all triangle names are consistent
                if not (tri1 == ratio_tri1_1 == ratio_tri1_2 and tri2 == ratio_tri2_1 == ratio_tri2_2):
                    return GeometricError(
                        tier=ErrorTier.TIER1_THEOREM_CALL_SYNTAX_VIOLATION,
                        message="Inconsistent triangle names in conclusion",
                        details=f"All references to the first triangle should be {tri1} and second triangle should be {tri2}"
                    )

                # Create area variables for both triangles
                norm_tri1 = self.normalize_triangle(tri1)
                norm_tri2 = self.normalize_triangle(tri2)

                if norm_tri1 not in self.triangle_areas:
                    self.triangle_areas[norm_tri1] = Real(f"areaTriangle_{norm_tri1}")
                    self.solver.add(self.triangle_areas[norm_tri1] >= 0)

                if norm_tri2 not in self.triangle_areas:
                    self.triangle_areas[norm_tri2] = Real(f"areaTriangle_{norm_tri2}")
                    self.solver.add(self.triangle_areas[norm_tri2] >= 0)

                area_tri1 = self.triangle_areas[norm_tri1]
                area_tri2 = self.triangle_areas[norm_tri2]

                # Get the similarity ratio variable
                norm_similar_pair = self.normalize_similar_triangles(tri1, tri2)
                if norm_similar_pair not in self.triangle_ratios:
                    ratio_var_name = f"ratio_{norm_similar_pair[0]}_{norm_similar_pair[1]}"
                    self.triangle_ratios[norm_similar_pair] = Real(ratio_var_name)

                ratio_var = self.triangle_ratios[norm_similar_pair]

                # Add the constraint: area_tri1 = area_tri2 * ratio^2
                self.solver.add(area_tri1 == area_tri2 * ratio_var * ratio_var)

                print(f"Added area ratio constraint: Area({tri1}) = Area({tri2}) * [Ratio({tri1},{tri2})]²")
                return None
            else:
                return GeometricError(
                    tier=ErrorTier.TIER1_THEOREM_CALL_SYNTAX_VIOLATION,
                    message=f"Unsupported version {version} for similar_triangle_property_area_square_ratio",
                    details="Only version 1 is supported"
                )

        # For the quadrilateral_perimeter_formula theorem
        elif theorem_name == "quadrilateral_perimeter_formula":
            version = args[0]
            if version == "1":
                if len(args) < 2:
                    return GeometricError(
                        tier=ErrorTier.TIER1_THEOREM_CALL_SYNTAX_VIOLATION,
                        message="Missing quadrilateral name for quadrilateral_perimeter_formula",
                        details="Expected: quadrilateral_perimeter_formula(1, quadrilateral)"
                    )

                quad = args[1].strip()  # e.g., "ABCD"

                # Extract the sides from the conclusion using a more flexible pattern
                # Handle different possible formats of the conclusion
                match = re.search(
                    r'Equal\(Add\(LengthOfLine\((\w+)\),LengthOfLine\((\w+)\),LengthOfLine\((\w+)\),LengthOfLine\((\w+)\)\),(PerimeterOfQuadrilateral\((\w+)\)|perimeter_(\w+))\)',
                    conclusions[0]
                )

                if match:
                    side1, side2, side3, side4 = match.groups()[:4]
                    # The perimeter part could be in different forms, so handle that flexibly
                    perimeter_quad = match.group(6) if match.group(6) else match.group(7) if match.group(7) else quad

                    # Verify that the quadrilateral names match if a name was specified
                    if perimeter_quad != quad:
                        return GeometricError(
                            tier=ErrorTier.TIER1_THEOREM_CALL_SYNTAX_VIOLATION,
                            message=f"Quadrilateral name mismatch: {perimeter_quad} vs {quad}",
                            details=f"The quadrilateral in the conclusion must match the one in the theorem call"
                        )

                    # Create length variables for each side
                    side1_var = self.add_length(side1[0], side1[1])
                    side2_var = self.add_length(side2[0], side2[1])
                    side3_var = self.add_length(side3[0], side3[1])
                    side4_var = self.add_length(side4[0], side4[1])

                    # Create or get perimeter variable
                    if not hasattr(self, "quadrilateral_perimeters"):
                        self.quadrilateral_perimeters = {}

                    perimeter_var = Real(f"perimeter_{quad}")
                    self.quadrilateral_perimeters[quad] = perimeter_var

                    # Add constraint: perimeter = sum of sides
                    self.solver.add(perimeter_var == side1_var + side2_var + side3_var + side4_var)

                    print(
                        f"Added quadrilateral perimeter constraint: perimeter({quad}) = {side1} + {side2} + {side3} + {side4}")
                    return None
                else:
                    # Try a simpler pattern that doesn't rely on the PerimeterOfQuadrilateral term
                    match = re.search(
                        r'Equal\(Add\(LengthOfLine\((\w+)\),LengthOfLine\((\w+)\),LengthOfLine\((\w+)\),LengthOfLine\((\w+)\)\),(.*?)\)',
                        conclusions[0]
                    )

                    if match:
                        side1, side2, side3, side4 = match.groups()[:4]

                        # Create length variables for each side
                        side1_var = self.add_length(side1[0], side1[1])
                        side2_var = self.add_length(side2[0], side2[1])
                        side3_var = self.add_length(side3[0], side3[1])
                        side4_var = self.add_length(side4[0], side4[1])

                        # Create or get perimeter variable
                        if not hasattr(self, "quadrilateral_perimeters"):
                            self.quadrilateral_perimeters = {}

                        perimeter_var = Real(f"perimeter_{quad}")
                        self.quadrilateral_perimeters[quad] = perimeter_var

                        # Add constraint: perimeter = sum of sides
                        self.solver.add(perimeter_var == side1_var + side2_var + side3_var + side4_var)

                        print(
                            f"Added quadrilateral perimeter constraint: perimeter({quad}) = {side1} + {side2} + {side3} + {side4}")
                        return None
                    else:
                        return GeometricError(
                            tier=ErrorTier.TIER1_THEOREM_CALL_SYNTAX_VIOLATION,
                            message="Conclusion format error for quadrilateral_perimeter_formula",
                            details=f"Expected conclusion with four side lengths but got {conclusions[0]}"
                        )
            else:
                return GeometricError(
                    tier=ErrorTier.TIER1_THEOREM_CALL_SYNTAX_VIOLATION,
                    message=f"Unsupported version {version} for quadrilateral_perimeter_formula"
                )

        elif theorem_name == "congruent_triangle_judgment_aas":
            version = args[0]
            if version in {"1", "2", "3"}:
                match = re.search(r'CongruentBetweenTriangle\((\w+),(\w+)\)', conclusions[0])
                if match:
                    tri1, tri2 = match.groups()
                    canonical_pair = self.canonicalize_congruent_triangle_pair(tri1, tri2)
                    if canonical_pair not in self.congruent_triangles:
                        self.congruent_triangles.append(canonical_pair)
                    print(f"Added congruent triangles via AAS: {tri1} and {tri2} (canonical: {canonical_pair})")
                else:
                    return GeometricError(
                        tier=ErrorTier.TIER1_THEOREM_CALL_SYNTAX_VIOLATION,
                        message="Conclusion format error for congruent_triangle_judgment_aas",
                        details=f"Expected CongruentBetweenTriangle(...) but got {conclusions[0]}"
                    )
            else:
                return GeometricError(
                    tier=ErrorTier.TIER1_THEOREM_CALL_SYNTAX_VIOLATION,
                    message=f"Unsupported version {version} for congruent_triangle_judgment_aas",
                    details="Supported versions are 1, 2, and 3"
                )




        elif theorem_name == "arc_addition_measure":
            version = args[0]
            if version == "1":
                # Expected conclusion: "Equal(MeasureOfArc(ODB),Add(MeasureOfArc(ODA),MeasureOfArc(OAB)))"
                # We need to extract the three arc names: total_arc, arc1, and arc2
                match = re.search(
                    r'Equal\(MeasureOfArc\((\w+)\),Add\(MeasureOfArc\((\w+)\),MeasureOfArc\((\w+)\)\)\)',
                    conclusions[0]
                )

                if match:
                    total_arc, arc1, arc2 = match.groups()  # e.g., "ODB", "ODA", "OAB"

                    # Get (or create) Z3 variables for all three arcs
                    total_arc_var = self.add_arc(total_arc)
                    arc1_var = self.add_arc(arc1)
                    arc2_var = self.add_arc(arc2)

                    # Add the constraint that total_arc = arc1 + arc2
                    self.solver.add(total_arc_var == arc1_var + arc2_var)

                    print(
                        f"Added arc addition constraint: MeasureOfArc({total_arc}) = MeasureOfArc({arc1}) + MeasureOfArc({arc2})")
                    return None
                else:
                    return GeometricError(
                        tier=ErrorTier.TIER1_THEOREM_CALL_SYNTAX_VIOLATION,
                        message="Conclusion format error for arc_addition_measure",
                        details=f"Expected pattern Equal(MeasureOfArc(XX),Add(MeasureOfArc(YY),MeasureOfArc(ZZ))) but got {conclusions[0]}"
                    )
            else:
                return GeometricError(
                    tier=ErrorTier.TIER1_THEOREM_CALL_SYNTAX_VIOLATION,
                    message=f"Unsupported version {version} for arc_addition_measure"
                )

        elif theorem_name == "midsegment_of_quadrilateral_property_length":
            version = args[0]
            if version == "1":
                segment = args[1].strip()
                quad = args[2].strip()

                # Check the conclusion format
                # Expected conclusion: "Equal(Add(LengthOfLine(AD),LengthOfLine(BC)),Mul(LengthOfLine(EF),2))"
                match = re.search(
                    r'Equal\(Add\(LengthOfLine\((\w+)\),LengthOfLine\((\w+)\)\),Mul\(LengthOfLine\(' +
                    re.escape(segment) + r'\),2\)\)',
                    conclusions[0]
                )

                if match:
                    side1, side2 = match.groups()

                    # Get length variables for all segments
                    segment_var = self.add_length(segment[0], segment[1])
                    side1_var = self.add_length(side1[0], side1[1])
                    side2_var = self.add_length(side2[0], side2[1])

                    # Add the constraint: segment = (side1 + side2) / 2
                    # Or equivalently: 2 * segment = side1 + side2
                    self.solver.add(segment_var * 2 == side1_var + side2_var)

                    print(f"Added midsegment property constraint: 2 * {segment} = {side1} + {side2}")
                    return None
                else:
                    return GeometricError(
                        tier=ErrorTier.TIER1_THEOREM_CALL_SYNTAX_VIOLATION,
                        message="Conclusion format error for midsegment_of_quadrilateral_property_length",
                        details=f"Expected pattern Equal(Add(LengthOfLine(XX),LengthOfLine(YY)),Mul(LengthOfLine({segment}),2)) but got {conclusions[0]}"
                    )
            else:
                return GeometricError(
                    tier=ErrorTier.TIER1_THEOREM_CALL_SYNTAX_VIOLATION,
                    message=f"Unsupported version {version} for midsegment_of_quadrilateral_property_length"
                )
        elif theorem_name == "parallelogram_area_formula_sine":
            version = args[0]
            if version == "1":
                # Expected conclusion format: "Equal(AreaOfQuadrilateral(DACB),Mul(LengthOfLine(DA),LengthOfLine(AC),Sin(MeasureOfAngle(DAC))))"
                c = conclusions[0]
                pat = r"Equal\(AreaOfQuadrilateral\((\w+)\),Mul\(LengthOfLine\((\w+)\),LengthOfLine\((\w+)\),Sin\(MeasureOfAngle\((\w{3})\)\)\)\)"
                mm = re.match(pat, c)
                if mm:
                    quad_name, side1, side2, angle_name = mm.groups()
                    # Ensure an area variable exists for the quadrilateral.
                    if quad_name not in self.quad_areas:
                        self.quad_areas[quad_name] = Real(f"AreaOfQuadrilateral_{quad_name}")
                        self.solver.add(self.quad_areas[quad_name] >= 0)
                    area_var = self.quad_areas[quad_name]
                    # Get the side length variables.
                    side1_var = self.add_length(side1[0], side1[1])
                    side2_var = self.add_length(side2[0], side2[1])
                    # Get the angle variable.
                    angle_var = self.add_angle(angle_name[0], angle_name[1], angle_name[2])

                    # Try to evaluate the angle numerically so we can compute its sine.
                    if self.solver.check() == sat:
                        model = self.solver.model()

                        # Check if angle is uniquely determined
                        angle_unique = False
                        angle_val = None
                        sin_val = None

                        try:
                            # Get the current angle value from the model
                            a_val_str = model.eval(angle_var).as_decimal(10)
                            if a_val_str.endswith('?'):
                                a_val_str = a_val_str[:-1]
                            angle_val = float(a_val_str)

                            # Check if this value is uniquely determined
                            temp_solver = Solver()
                            for c in self.solver.assertions():
                                temp_solver.add(c)

                            epsilon = 1e-6
                            temp_solver.add(Or(
                                angle_var < angle_val - epsilon,
                                angle_var > angle_val + epsilon
                            ))

                            if temp_solver.check() == unsat:
                                # Angle is uniquely determined
                                angle_unique = True
                                import math
                                sin_val = math.sin(math.radians(angle_val))
                                print(f"Angle {angle_name} has unique value {angle_val}°, sin = {sin_val}")

                                # Add the constraint with the computed sine value
                                self.solver.add(area_var == side1_var * side2_var * sin_val)
                                print(
                                    f"Added parallelogram area constraint with known sine value: AreaOfQuadrilateral({quad_name}) = LengthOfLine({side1}) * LengthOfLine({side2}) * {sin_val}")
                            else:
                                # Angle is not uniquely determined, create a variable for the sine
                                sin_var_name = f"sin_{angle_name}"
                                if sin_var_name not in self.variables:
                                    self.variables[sin_var_name] = Real(sin_var_name)
                                    self.solver.add(self.variables[sin_var_name] >= 0)
                                    self.solver.add(self.variables[sin_var_name] <= 1)
                                sin_var = self.variables[sin_var_name]

                                # Add the constraint with the sine variable
                                self.solver.add(area_var == side1_var * side2_var * sin_var)
                                print(
                                    f"Added parallelogram area constraint with sine variable: AreaOfQuadrilateral({quad_name}) = LengthOfLine({side1}) * LengthOfLine({side2}) * sin({angle_name})")
                        except Exception as e:
                            print(f"Error checking angle: {e}")
                            # Create a variable for the sine as a fallback
                            sin_var_name = f"sin_{angle_name}"
                            if sin_var_name not in self.variables:
                                self.variables[sin_var_name] = Real(sin_var_name)
                                self.solver.add(self.variables[sin_var_name] >= 0)
                                self.solver.add(self.variables[sin_var_name] <= 1)
                            sin_var = self.variables[sin_var_name]

                            # Add the constraint with the sine variable
                            self.solver.add(area_var == side1_var * side2_var * sin_var)
                            print(
                                f"Added parallelogram area constraint with sine variable (after error): AreaOfQuadrilateral({quad_name}) = LengthOfLine({side1}) * LengthOfLine({side2}) * sin({angle_name})")

                        return None
                    else:
                        # Get the contradictory constraints to provide better feedback
                        contradictory_constraints = self.find_contradictory_constraints()
                        details = "No specific contradictory constraints found."

                        if contradictory_constraints:
                            details = "Contradictory constraints:\n"
                            for constraint in contradictory_constraints:
                                details += f"  {constraint}\n"

                        # Include angle constraints
                        angle_constraints = []
                        for c in self.solver.assertions():
                            c_str = str(c)
                            if f"angle_{angle_name}" in c_str or f"sin_" in c_str:
                                angle_constraints.append(self.format_constraint(c_str))

                        if angle_constraints:
                            details += "\nRelevant angle constraints:\n"
                            for constraint in angle_constraints:
                                details += f"  {constraint}\n"

                        # Include length constraints
                        length_constraints = []
                        for c in self.solver.assertions():
                            c_str = str(c)
                            if (f"length_{side1}" in c_str or
                                    f"length_{side2}" in c_str):
                                length_constraints.append(self.format_constraint(c_str))

                        if length_constraints:
                            details += "\nRelevant length constraints:\n"
                            for constraint in length_constraints:
                                details += f"  {constraint}\n"

                        return GeometricError(
                            tier=ErrorTier.TIER2_PREMISE_VIOLATION,
                            message="Solver unsat when trying to evaluate angles for parallelogram_area_formula_sine",
                            details=details
                        )
                else:
                    return GeometricError(
                        tier=ErrorTier.TIER1_THEOREM_CALL_SYNTAX_VIOLATION,
                        message="Conclusion format error for parallelogram_area_formula_sine",
                        details=f"Expected pattern Equal(AreaOfQuadrilateral(XXXX),Mul(LengthOfLine(XX),LengthOfLine(XX),Sin(MeasureOfAngle(XXX)))) but got {conclusions[0]}"
                    )
            else:
                return GeometricError(
                    tier=ErrorTier.TIER1_THEOREM_CALL_SYNTAX_VIOLATION,
                    message=f"Unsupported version {version} for parallelogram_area_formula_sine"
                )




        elif theorem_name == "isosceles_triangle_property_line_coincidence":

            version = args[0]

            if version in {"1", "2", "3"}:

                if len(args) < 3:
                    return GeometricError(

                        tier=ErrorTier.TIER1_THEOREM_CALL_SYNTAX_VIOLATION,

                        message="Insufficient arguments for isosceles_triangle_property_line_coincidence",

                        details=f"Expected: isosceles_triangle_property_line_coincidence({version}, triangle, point)"

                    )

                triangle = args[1].strip()  # e.g., "ABC"

                point = args[2].strip()  # e.g., "M"

                line = triangle[0] + point  # e.g., "AM"

                # Determine the conclusions based on version

                if version == "1":

                    # Conclusions: IsMedianOfTriangle(AM,ABC), IsBisectorOfAngle(AM,CAB)

                    # Process the first conclusion - Making it a median

                    if not hasattr(self, "medians"):
                        self.medians = []

                    self.medians.append((line, triangle))

                    print(f"Added median fact: {line} is a median of triangle {triangle}")

                    # Process the second conclusion - Making it an angle bisector

                    opposite_vertices = [v for v in triangle if v != line[0]]  # e.g., ["B", "C"]

                    angle_name = opposite_vertices[0] + line[0] + opposite_vertices[1]  # e.g., "BAC"

                    if not hasattr(self, "angle_bisectors"):
                        self.angle_bisectors = []

                    self.angle_bisectors.append((line, angle_name))

                    # Add constraint that both angles are equal (definition of angle bisector)

                    vertex = line[0]  # e.g., "A"

                    angle_side1 = opposite_vertices[0]  # e.g., "B"

                    angle_side2 = opposite_vertices[1]  # e.g., "C"

                    bisector_other = point  # e.g., "M"

                    angle1 = angle_side1 + vertex + bisector_other  # e.g., "BAM"

                    angle2 = bisector_other + vertex + angle_side2  # e.g., "MAC"

                    angle1_var = self.add_angle(angle1[0], angle1[1], angle1[2])

                    angle2_var = self.add_angle(angle2[0], angle2[1], angle2[2])

                    self.solver.add(angle1_var == angle2_var)

                    print(f"Added angle bisector constraint: angle {angle1} = angle {angle2}")


                elif version == "2":

                    # Conclusions: IsAltitudeOfTriangle(AM,ABC), IsBisectorOfAngle(AM,CAB)

                    # Process the altitude conclusion

                    if not hasattr(self, "triangle_altitudes"):
                        self.triangle_altitudes = {}

                    if triangle not in self.triangle_altitudes:
                        self.triangle_altitudes[triangle] = []

                    self.triangle_altitudes[triangle].append(line)

                    # Determine the vertices involved

                    altitude_start = line[0]  # e.g., "A"

                    altitude_end = line[1]  # e.g., "M"

                    # Find the opposite side to the altitude's starting point

                    opposite_vertices = [v for v in triangle if v != altitude_start]  # e.g., ["B", "C"]

                    # Add right angle constraints



                    # Process the angle bisector conclusion

                    if not hasattr(self, "angle_bisectors"):
                        self.angle_bisectors = []

                    angle_name = opposite_vertices[0] + altitude_start + opposite_vertices[1]  # e.g., "BAC"

                    self.angle_bisectors.append((line, angle_name))

                    # Add angle bisector constraints

                    vertex = altitude_start  # e.g., "A"

                    angle_side1 = opposite_vertices[0]  # e.g., "B"

                    angle_side2 = opposite_vertices[1]  # e.g., "C"

                    bisector_other = altitude_end  # e.g., "M"

                    angle1 = angle_side1 + vertex + bisector_other  # e.g., "BAM"

                    angle2 = bisector_other + vertex + angle_side2  # e.g., "MAC"

                    angle1_var = self.add_angle(angle1[0], angle1[1], angle1[2])

                    angle2_var = self.add_angle(angle2[0], angle2[1], angle2[2])

                    self.solver.add(angle1_var == angle2_var)

                    print(f"Added angle bisector constraint: angle {angle1} = angle {angle2}")


                elif version == "3":

                    # Conclusions: IsAltitudeOfTriangle(AM,ABC), IsMedianOfTriangle(AM,ABC)

                    # Process the altitude conclusion

                    if not hasattr(self, "triangle_altitudes"):
                        self.triangle_altitudes = {}

                    if triangle not in self.triangle_altitudes:
                        self.triangle_altitudes[triangle] = []

                    self.triangle_altitudes[triangle].append(line)

                    # Determine the vertices involved

                    altitude_start = line[0]  # e.g., "A"

                    altitude_end = line[1]  # e.g., "M"

                    # Find the opposite side to the altitude's starting point

                    opposite_vertices = [v for v in triangle if v != altitude_start]  # e.g., ["B", "C"]

                    # Add right angle constraints

                    for opposite_vertex in opposite_vertices:
                        angle_name = altitude_end + altitude_start + opposite_vertex  # e.g., "MAB"

                        angle_var = self.add_angle(angle_name[0], angle_name[1], angle_name[2])

                        self.solver.add(angle_var == 90)

                        print(f"Added 90° angle constraint for altitude: angle {angle_name} = 90°")

                    # Process the median conclusion

                    if not hasattr(self, "medians"):
                        self.medians = []

                    self.medians.append((line, triangle))

                    print(f"Added median fact: {line} is a median of triangle {triangle}")

                print(f"Added isosceles triangle property for version {version}: line {line} in triangle {triangle}")

                return None

            else:

                return GeometricError(

                    tier=ErrorTier.TIER1_THEOREM_CALL_SYNTAX_VIOLATION,

                    message=f"Unsupported version {version} for isosceles_triangle_property_line_coincidence",

                    details="Supported versions are 1, 2, and 3"

                )



        elif theorem_name == "mirror_congruent_triangle_judgment_sas":
            version = args[0]
            if version == "1":
                match = re.search(r'MirrorCongruentBetweenTriangle\((\w+),(\w+)\)', conclusions[0])
                if match:
                    tri1, tri2 = match.groups()
                    canonical_pair = self.canonicalize_mirror_congruent_triangle_pair(tri1, tri2)

                    if canonical_pair not in self.mirror_congruent_triangles:
                        self.mirror_congruent_triangles.append(canonical_pair)

                    print(f"Added mirror congruent triangles via SAS: {tri1} and {tri2} (canonical: {canonical_pair})")
                else:
                    return GeometricError(
                        tier=ErrorTier.TIER1_THEOREM_CALL_SYNTAX_VIOLATION,
                        message="Conclusion format error for mirror_congruent_triangle_judgment_sas",
                        details=f"Expected MirrorCongruentBetweenTriangle(...) but got {conclusions[0]}"
                    )




        elif theorem_name == "diameter_of_circle_judgment_pass_centre":
            version = args[0]
            if version == "1":
                # Expected conclusion: "IsDiameterOfCircle(AB,O)"
                match = re.search(r'IsDiameterOfCircle\((\w+),(\w+)\)', conclusions[0])

                if match:
                    diameter_line, circle_name = match.groups()  # e.g., "AB", "O"

                    # Record that this line is a diameter of the given circle
                    self.is_diameter_of_circle.append((diameter_line, circle_name))

                    # Also add the reversed line as a diameter
                    self.is_diameter_of_circle.append((diameter_line[::-1], circle_name))

                    # If circle_radii and circle_diameters exist, set up the relationship
                    if hasattr(self, "circle_radii") and hasattr(self, "circle_diameters"):
                        if circle_name in self.circle_radii:
                            # Get or create diameter variable
                            diam_name = f"diameter_{circle_name}"
                            if diam_name not in self.circle_diameters:
                                self.circle_diameters[diam_name] = Real(diam_name)
                                self.solver.add(self.circle_diameters[diam_name] >= 0)

                            # Get or create length variable for the diameter line
                            diameter_var = self.add_length(diameter_line[0], diameter_line[1])

                            # Set diameter length = diameter variable
                            self.solver.add(diameter_var == self.circle_diameters[diam_name])

                            # Set diameter = 2 * radius relationship
                            radius_var = self.circle_radii[circle_name]
                            self.solver.add(self.circle_diameters[diam_name] == 2 * radius_var)

                    print(f"Added diameter fact: {diameter_line} is a diameter of circle {circle_name}")
                    return None
                else:
                    return GeometricError(
                        tier=ErrorTier.TIER1_THEOREM_CALL_SYNTAX_VIOLATION,
                        message="Conclusion format error for diameter_of_circle_judgment_pass_centre",
                        details=f"Expected IsDiameterOfCircle(XX,Y) pattern but got {conclusions[0]}"
                    )
            else:
                return GeometricError(
                    tier=ErrorTier.TIER1_THEOREM_CALL_SYNTAX_VIOLATION,
                    message=f"Unsupported version {version} for diameter_of_circle_judgment_pass_centre"
                )










        elif theorem_name == "mirror_congruent_triangle_property_angle_equal":
            version = args[0]
            if version == "1":
                match = re.search(r'Equal\(MeasureOfAngle\((\w+)\),MeasureOfAngle\((\w+)\)\)', conclusions[0])
                if match:
                    angle1, angle2 = match.groups()
                    angle1_var = self.add_angle(angle1[0], angle1[1], angle1[2])
                    angle2_var = self.add_angle(angle2[0], angle2[1], angle2[2])
                    self.solver.add(angle1_var == angle2_var)
                    print(
                        f"Added mirror congruent triangle property: MeasureOfAngle({angle1}) = MeasureOfAngle({angle2})")
                else:
                    return GeometricError(
                        tier=ErrorTier.TIER1_THEOREM_CALL_SYNTAX_VIOLATION,
                        message="Conclusion format error for mirror_congruent_triangle_property_angle_equal",
                        details=f"Expected format: Equal(MeasureOfAngle(XXX),MeasureOfAngle(YYY)) but got {conclusions[0]}"
                    )



        # In the adding_conclution method

        # In the adding_conclution method
        elif theorem_name == "right_triangle_property_length_of_median":
            version = args[0]
            if version == "1":
                # Expected conclusion: ["Equal(Mul(LengthOfLine(EM),2),LengthOfLine(BC))"]
                match = re.search(r'Equal\(Mul\(LengthOfLine\((\w+)\),2\),LengthOfLine\((\w+)\)\)', conclusions[0])
                if not match:
                    return GeometricError(
                        tier=ErrorTier.TIER1_THEOREM_CALL_SYNTAX_VIOLATION,
                        message="Invalid conclusion format for right_triangle_property_length_of_median",
                        details="Expected format: Equal(Mul(LengthOfLine(median),2),LengthOfLine(hypotenuse))"
                    )

                median_line = match.group(1)  # "EM"
                hypotenuse = match.group(2)  # "BC"

                # Add the constraint: median_length * 2 = hypotenuse_length
                median_length = self.add_length(median_line[0], median_line[1])
                hypotenuse_length = self.add_length(hypotenuse[0], hypotenuse[1])

                self.solver.add(median_length * 2 == hypotenuse_length)
                print(
                    f"Added right triangle median property: 2 * LengthOfLine({median_line}) = LengthOfLine({hypotenuse})")

                return None



        elif theorem_name == "mirror_congruent_triangle_judgment_aas":

            version = args[0]

            if version in {"1", "2", "3"}:  # Handle all three versions

                match = re.search(r'MirrorCongruentBetweenTriangle\((\w+),(\w+)\)', conclusions[0])

                if match:

                    tri1, tri2 = match.groups()

                    canonical_pair = self.canonicalize_mirror_congruent_triangle_pair(tri1, tri2)

                    if canonical_pair not in self.mirror_congruent_triangles:
                        self.mirror_congruent_triangles.append(canonical_pair)

                    print(f"Added mirror congruent triangles via AAS: {tri1} and {tri2} (canonical: {canonical_pair})")

                else:

                    return GeometricError(

                        tier=ErrorTier.TIER1_THEOREM_CALL_SYNTAX_VIOLATION,

                        message="Conclusion format error for mirror_congruent_triangle_judgment_aas",

                        details=f"Expected MirrorCongruentBetweenTriangle(...) but got {conclusions[0]}"

                    )

            else:

                return GeometricError(

                    tier=ErrorTier.TIER1_THEOREM_CALL_SYNTAX_VIOLATION,

                    message=f"Unsupported version {version} for mirror_congruent_triangle_judgment_aas",

                    details="Supported versions are 1, 2, and 3"

                )


        elif theorem_name == "parallel_judgment_par_par":
            version = args[0]
            if version == "1":
                match = re.search(r'ParallelBetweenLine\((\w+),(\w+)\)', conclusions[0])
                if match:
                    line1, line2 = match.groups()

                    # Add the new parallel relationship
                    self.parallel_pairs.add((line1, line2))
                    self.parallel_pairs.add((line2, line1))

                    print(f"Added transitive parallel relationship: {line1} || {line2} (by transitivity)")
                else:
                    return GeometricError(
                        tier=ErrorTier.TIER1_THEOREM_CALL_SYNTAX_VIOLATION,
                        message="Conclusion format error for parallel_judgment_par_par",
                        details=f"Expected ParallelBetweenLine(...) but got {conclusions[0]}"
                    )

        elif theorem_name == "mirror_congruent_triangle_property_line_equal":

            version = args[0]

            if version == "1":

                match = re.search(r'Equal\(LengthOfLine\((\w+)\),LengthOfLine\((\w+)\)\)', conclusions[0])

                if match:

                    line1, line2 = match.groups()

                    line1_var = self.add_length(line1[0], line1[1])

                    line2_var = self.add_length(line2[0], line2[1])

                    self.solver.add(line1_var == line2_var)

                    print(f"Added mirror congruent triangle property: LengthOfLine({line1}) = LengthOfLine({line2})")

                else:

                    return GeometricError(

                        tier=ErrorTier.TIER1_THEOREM_CALL_SYNTAX_VIOLATION,

                        message="Conclusion format error for mirror_congruent_triangle_property_line_equal",

                        details=f"Expected format: Equal(LengthOfLine(XX),LengthOfLine(YY)) but got {conclusions[0]}"

                    )


        elif theorem_name == "midsegment_of_triangle_judgment_midpoint":

            version = args[0]

            if version == "1":

                match = re.search(r'IsMidsegmentOfTriangle\((\w+),(\w+)\)', conclusions[0])

                if match:

                    segment, triangle = match.groups()

                    print(f"Added midsegment fact: {segment} is a midsegment of triangle {triangle}")

                else:

                    return GeometricError(

                        tier=ErrorTier.TIER1_THEOREM_CALL_SYNTAX_VIOLATION,

                        message="Conclusion format error for midsegment_of_triangle_judgment_midpoint",

                        details=f"Expected IsMidsegmentOfTriangle(...) but got {conclusions[0]}"

                    )


        elif theorem_name == "midsegment_of_triangle_property_length":

            version = args[0]

            if version == "1":

                match = re.search(r'Equal\(LengthOfLine\((\w+)\),Mul\(LengthOfLine\((\w+)\),(\d+/\d+)\)\)',
                                  conclusions[0])

                if match:

                    segment, parallel_side, factor_str = match.groups()

                    # Get length variables

                    segment_var = self.add_length(segment[0], segment[1])

                    parallel_side_var = self.add_length(parallel_side[0], parallel_side[1])

                    # Parse the factor (typically 1/2)

                    try:

                        from fractions import Fraction

                        factor_val = float(Fraction(factor_str))

                    except Exception as e:

                        print(f"Error parsing factor {factor_str}: {e}, defaulting to 0.5")

                        factor_val = 0.5

                    # Add constraint: midsegment length = factor * parallel side length

                    self.solver.add(segment_var == factor_val * parallel_side_var)

                    print(
                        f"Added midsegment length constraint: LengthOfLine({segment}) = {factor_val} * LengthOfLine({parallel_side})")

                else:

                    return GeometricError(

                        tier=ErrorTier.TIER1_THEOREM_CALL_SYNTAX_VIOLATION,

                        message="Conclusion format error for midsegment_of_triangle_property_length",

                        details=f"Expected format: Equal(LengthOfLine(XX),Mul(LengthOfLine(YY),factor)) but got {conclusions[0]}"

                    )



        # Then add these handlers in the if-elif chain:
        elif theorem_name == "congruent_triangle_property_line_equal":
            version = args[0]
            if version == "1":
                match = re.search(r'Equal\(LengthOfLine\((\w+)\),LengthOfLine\((\w+)\)\)', conclusions[0])
                if match:
                    line1, line2 = match.groups()
                    line1_var = self.add_length(line1[0], line1[1])
                    line2_var = self.add_length(line2[0], line2[1])
                    self.solver.add(line1_var == line2_var)
                    print(f"Added congruent triangle property: LengthOfLine({line1}) = LengthOfLine({line2})")
                else:
                    return GeometricError(
                        tier=ErrorTier.TIER1_THEOREM_CALL_SYNTAX_VIOLATION,
                        message="Conclusion format error for congruent_triangle_property_line_equal",
                        details=f"Expected format: Equal(LengthOfLine(XX),LengthOfLine(YY)) but got {conclusions[0]}"
                    )

        elif theorem_name == "congruent_triangle_property_angle_equal":
            version = args[0]
            if version == "1":
                match = re.search(r'Equal\(MeasureOfAngle\((\w+)\),MeasureOfAngle\((\w+)\)\)', conclusions[0])
                if match:
                    angle1, angle2 = match.groups()
                    angle1_var = self.add_angle(angle1[0], angle1[1], angle1[2])
                    angle2_var = self.add_angle(angle2[0], angle2[1], angle2[2])
                    self.solver.add(angle1_var == angle2_var)
                    print(f"Added congruent triangle property: MeasureOfAngle({angle1}) = MeasureOfAngle({angle2})")
                else:
                    return GeometricError(
                        tier=ErrorTier.TIER1_THEOREM_CALL_SYNTAX_VIOLATION,
                        message="Conclusion format error for congruent_triangle_property_angle_equal",
                        details=f"Expected format: Equal(MeasureOfAngle(XXX),MeasureOfAngle(YYY)) but got {conclusions[0]}"
                    )


        elif theorem_name == "median_of_triangle_judgment":

            version = args[0]

            if version == "1":

                # Expected conclusion: ["IsMedianOfTriangle(EM,EBC)"]

                median_match = re.search(r'IsMedianOfTriangle\((\w+),(\w+)\)', conclusions[0])

                if not median_match:
                    return GeometricError(

                        tier=ErrorTier.TIER1_THEOREM_CALL_SYNTAX_VIOLATION,

                        message="Invalid conclusion format for median_of_triangle_judgment",

                        details="Expected format: IsMedianOfTriangle(line,triangle)"

                    )

                median_line = median_match.group(1)  # "EM"

                triangle = median_match.group(2)  # "EBC"

                # Store the median information

                if not hasattr(self, "medians"):
                    self.medians = []

                self.medians.append((median_line, triangle))

                print(f"Recorded median: IsMedianOfTriangle({median_line},{triangle})")

                return None

        elif theorem_name == "incenter_of_triangle_judgment_intersection":
            incenter_match = re.search(r'IsIncenterOfTriangle\((\w+),(\w+)\)', conclusions[0])
            if not incenter_match:
                return GeometricError(
                    tier=ErrorTier.TIER1_THEOREM_CALL_SYNTAX_VIOLATION,
                    message="Invalid conclusion format for incenter_of_triangle_judgment_intersection",
                    details="Expected format: IsIncenterOfTriangle(point,triangle)"
                )

            point, triangle = incenter_match.groups()

            # Store the incenter fact for future reference
            if not hasattr(self, "incenters"):
                self.incenters = {}
            self.incenters[triangle] = point

            print(f"Recorded incenter fact: {point} is the incenter of triangle {triangle}")
            return None


        elif theorem_name == "vertical_angle":
            version = args[0]
            if version == "1":
                # Expected conclusion: "Equal(MeasureOfAngle(DEB),MeasureOfAngle(CEA))"
                match = re.search(
                    r'Equal\(MeasureOfAngle\((\w{3})\),\s*MeasureOfAngle\((\w{3})\)\)',
                    conclusions[0]
                )

                if match:
                    angle1, angle2 = match.groups()

                    # Get (or create) angle variables
                    angle1_var = self.add_angle(angle1[0], angle1[1], angle1[2])
                    angle2_var = self.add_angle(angle2[0], angle2[1], angle2[2])

                    # Add the equality constraint
                    self.solver.add(angle1_var == angle2_var)

                    print(f"Added vertical angle constraint: {angle1} = {angle2}")
                    return None
                else:
                    return GeometricError(
                        tier=ErrorTier.TIER1_THEOREM_CALL_SYNTAX_VIOLATION,
                        message="Conclusion format error for vertical_angle",
                        details=f"Expected format: Equal(MeasureOfAngle(XXX),MeasureOfAngle(YYY)) but got {conclusions[0]}"
                    )
            else:
                return GeometricError(
                    tier=ErrorTier.TIER1_THEOREM_CALL_SYNTAX_VIOLATION,
                    message=f"Unsupported version {version} for vertical_angle"
                )




        elif theorem_name == "isosceles_triangle_judgment_angle_equal":

            # Expected theorem call: isosceles_triangle_judgment_angle_equal(1, triangle)

            # where triangle is a triangle name (e.g., "ABE")

            tri = args[1].strip()

            # Record that the triangle is isosceles by adding it and all its cyclic rotations

            # to an attribute (e.g. self.isosceles_triangles).

            def cyclic_rotations(s):

                rotations = set()

                for i in range(len(s)):
                    rotations.add(s[i:] + s[:i])

                return rotations

            rotations = cyclic_rotations(tri)

            if not hasattr(self, "isosceles_triangles"):
                self.isosceles_triangles = set()

            self.isosceles_triangles.update(rotations)

            print(f"Recorded isosceles triangle: {tri} and its rotations {rotations}")

            # Extract the equal angles from the premise to determine which sides should be equal

            angle_equal_match = re.search(r'Equal\(MeasureOfAngle\((\w{3})\),\s*MeasureOfAngle\((\w{3})\)\)', premise)

            if angle_equal_match:

                angle1, angle2 = angle_equal_match.groups()

                # Function to get the side opposite to an angle in a triangle

                def get_opposite_side(triangle, angle):

                    # The angle is specified by three points, where the middle point is the vertex

                    # The opposite side is formed by the other two points in the triangle that aren't the vertex

                    vertex = angle[1]  # Middle character is the vertex

                    return "".join(sorted([p for p in triangle if p != vertex]))

                # Get the opposite sides to the equal angles

                side1 = get_opposite_side(tri, angle1)

                side2 = get_opposite_side(tri, angle2)

                # Create length variables for both sides

                if len(side1) == 2 and len(side2) == 2:
                    side1_var = self.add_length(side1[0], side1[1])

                    side2_var = self.add_length(side2[0], side2[1])

                    # Add constraint that these sides are equal

                    self.solver.add(side1_var == side2_var)

                    print(f"Added isosceles triangle side equality: {side1} = {side2}")

            return None

        elif theorem_name == "parallelogram_judgment_parallel_and_parallel":
            version = args[0]
            if version == "1":
                # Check if we have at least the quadrilateral name
                if len(args) < 2:
                    return GeometricError(
                        tier=ErrorTier.TIER1_THEOREM_CALL_SYNTAX_VIOLATION,
                        message="Missing quadrilateral name for parallelogram_judgment_parallel_and_parallel",
                        details="Expected parallelogram_judgment_parallel_and_parallel(1, quadrilateral)"
                    )

                quad_name = args[1].strip()  # e.g., "BCDF"

                # Parse the premise to check polygon and parallel conditions
                premise_parts = premise.split('&')

                # First check if the polygon exists
                polygon_part = premise_parts[0].strip() if premise_parts else ""
                polygon_match = re.match(r'Polygon\((\w+)\)', polygon_part)

                if not polygon_match or polygon_match.group(1) != quad_name:
                    return GeometricError(
                        tier=ErrorTier.TIER2_PREMISE_VIOLATION,
                        message=f"Missing or incorrect polygon premise for {quad_name}",
                        details=f"Expected Polygon({quad_name}) in premise"
                    )

                # Check for parallel sides
                if len(premise_parts) < 3:
                    return GeometricError(
                        tier=ErrorTier.TIER2_PREMISE_VIOLATION,
                        message="Missing parallel sides conditions",
                        details="Need two ParallelBetweenLine statements in premise"
                    )

                # Parse the two parallel conditions
                parallel_matches = [re.match(r'ParallelBetweenLine\((\w+),(\w+)\)', part.strip())
                                    for part in premise_parts[1:3]]

                if not all(parallel_matches):
                    return GeometricError(
                        tier=ErrorTier.TIER2_PREMISE_VIOLATION,
                        message="Invalid parallel lines format in premise",
                        details="Expected format: ParallelBetweenLine(XX,YY)"
                    )

                # Verify that these parallel relations are recorded
                parallel_pairs = [(m.group(1), m.group(2)) for m in parallel_matches if m]
                for pair in parallel_pairs:
                    possible_pairs = [
                        pair,
                        (pair[1], pair[0]),
                        (pair[0][::-1], pair[1]),
                        (pair[0], pair[1][::-1]),
                        (pair[0][::-1], pair[1][::-1]),
                        (pair[1][::-1], pair[0]),
                        (pair[1], pair[0][::-1]),
                        (pair[1][::-1], pair[0][::-1])
                    ]

                    if not any(p in self.parallel_pairs or p[::-1] in self.parallel_pairs for p in possible_pairs):
                        return GeometricError(
                            tier=ErrorTier.TIER2_PREMISE_VIOLATION,
                            message=f"Parallel relation {pair} not established",
                            details=f"Known parallel pairs: {self.parallel_pairs}"
                        )

                # All checks passed, now record the quadrilateral as a parallelogram
                # Add the parallelogram and its cyclic variations to the parallelograms set
                if not hasattr(self, 'parallelograms'):
                    self.parallelograms = set()

                # Get all cyclic variations of the parallelogram
                parallelogram_variations = get_cyclic_variations(quad_name)
                self.parallelograms.update(parallelogram_variations)

                print(f"Added {quad_name} as a parallelogram based on parallel sides")
                return None
            elif version == "2":
                # Handle version 2 if needed
                print("Version 2 for parallelogram_judgment_parallel_and_parallel not implemented")
                return None


        elif theorem_name == "perpendicular_bisector_property_distance_equal":
            version = args[0]
            if version == "1":
                # Parse conclusion: "Equal(LengthOfLine(EA),LengthOfLine(EC))"
                match = re.search(r'Equal\(LengthOfLine\((\w+)\),LengthOfLine\((\w+)\)\)', conclusions[0])

                if match:
                    segment1, segment2 = match.groups()  # e.g., "EA", "EC"

                    # Get (or create) length variables for both segments
                    length1 = self.add_length(segment1[0], segment1[1])
                    length2 = self.add_length(segment2[0], segment2[1])

                    # Add the equality constraint
                    self.solver.add(length1 == length2)

                    print(
                        f"Added perpendicular bisector property constraint: LengthOfLine({segment1}) = LengthOfLine({segment2})")
                    return None
                else:
                    return GeometricError(
                        tier=ErrorTier.TIER1_THEOREM_CALL_SYNTAX_VIOLATION,
                        message="Conclusion format error for perpendicular_bisector_property_distance_equal",
                        details=f"Expected Equal(LengthOfLine(...),LengthOfLine(...)) but got {conclusions[0]}"
                    )
            else:
                return GeometricError(
                    tier=ErrorTier.TIER1_THEOREM_CALL_SYNTAX_VIOLATION,
                    message=f"Unsupported version {version} for perpendicular_bisector_property_distance_equal"
                )




        elif theorem_name == "triangle_area_formula_common":

            version = args[0]

            if version == "1":

                # Parse conclusion: "Equal(AreaOfTriangle(DCA),Mul(HeightOfTriangle(DCA),LengthOfLine(CA),1/2))"

                match = re.search(

                    r'Equal\(AreaOfTriangle\((\w+)\),Mul\(HeightOfTriangle\(\1\),LengthOfLine\((\w+)\),(\d+/\d+)\)\)',

                    conclusions[0]

                )

                if match:

                    triangle, base, factor_str = match.groups()

                    # Get or create area variable

                    normalized_triangle = ''.join(sorted(triangle))  # Normalize alphabetically as requested

                    if normalized_triangle not in self.triangle_areas:
                        self.triangle_areas[normalized_triangle] = Real(f"areaTriangle_{normalized_triangle}")

                        self.solver.add(self.triangle_areas[normalized_triangle] >= 0)

                    area_var = self.triangle_areas[normalized_triangle]

                    # Create height variable if it doesn't exist

                    if not hasattr(self, "triangle_heights"):
                        self.triangle_heights = {}

                    if triangle not in self.triangle_heights:

                        height_var = Real(f"heightTriangle_{triangle}")

                        self.triangle_heights[triangle] = height_var

                        self.solver.add(height_var >= 0)

                        print(f"Created height variable for triangle {triangle}")

                    else:

                        height_var = self.triangle_heights[triangle]

                    # Get base length variable

                    base_var = self.add_length(base[0], base[1])

                    # Parse the factor (usually 1/2)

                    try:

                        from fractions import Fraction

                        factor_val = float(Fraction(factor_str))

                    except Exception as e:

                        print(f"Error parsing factor {factor_str}: {e}, defaulting to 0.5")

                        factor_val = 0.5

                    # Add area formula constraint: area = (1/2) * height * base

                    self.solver.add(area_var == factor_val * height_var * base_var)

                    print(
                        f"Added triangle area constraint: AreaOfTriangle({triangle}) = {factor_val} * HeightOfTriangle({triangle}) * LengthOfLine({base})")

                    return None

                else:

                    return GeometricError(

                        tier=ErrorTier.TIER1_THEOREM_CALL_SYNTAX_VIOLATION,

                        message="Conclusion format error for triangle_area_formula_common",

                        details=f"Expected pattern not found in: {conclusions[0]}"

                    )

            else:

                return GeometricError(

                    tier=ErrorTier.TIER1_THEOREM_CALL_SYNTAX_VIOLATION,

                    message=f"Unsupported version {version} for triangle_area_formula_common"

                )





        elif theorem_name == "altitude_of_triangle_judgment":

            version = args[0]

            if version not in {"1", "2", "3"}:
                return GeometricError(

                    tier=ErrorTier.TIER1_THEOREM_CALL_SYNTAX_VIOLATION,

                    message=f"Unsupported version {version} for altitude_of_triangle_judgment",

                    details="Supported versions are 1, 2, and 3"

                )

            # Parse conclusion: "IsAltitudeOfTriangle(AD,ABC)"

            match = re.search(r'IsAltitudeOfTriangle\((\w+),(\w+)\)', conclusions[0])

            if not match:
                return GeometricError(

                    tier=ErrorTier.TIER1_THEOREM_CALL_SYNTAX_VIOLATION,

                    message="Conclusion format error for altitude_of_triangle_judgment",

                    details=f"Expected IsAltitudeOfTriangle(...) pattern but got {conclusions[0]}"

                )

            altitude_line = match.group(1)  # e.g., "AD"

            triangle = match.group(2)  # e.g., "ABC"

            # Extract altitude vertex, foot, and opposite vertices

            altitude_vertex = altitude_line[0]  # e.g., "A"

            altitude_foot = altitude_line[1]  # e.g., "D"

            opposite_vertices = [v for v in triangle if v != altitude_vertex]  # e.g., ["B", "C"]

            # Initialize triangle altitudes dictionary if it doesn't exist

            if not hasattr(self, "triangle_altitudes"):
                self.triangle_altitudes = {}

            # Initialize heights dictionary if it doesn't exist

            if not hasattr(self, "triangle_heights"):
                self.triangle_heights = {}

            # Add altitude information

            if triangle not in self.triangle_altitudes:
                self.triangle_altitudes[triangle] = []

            self.triangle_altitudes[triangle].append(altitude_line)

            # Create height variable for this triangle

            if triangle not in self.triangle_heights:
                height_var = Real(f"heightTriangle_{triangle}")

                self.triangle_heights[triangle] = height_var

                self.solver.add(height_var >= 0)

                # The height equals the altitude length

                altitude_length = self.add_length(altitude_line[0], altitude_line[1])

                self.solver.add(height_var == altitude_length)

            # Add collinearity constraint for the altitude foot and opposite side

            collinear_points = None

            if version == "1":

                # Version 1: Collinear(BDC)

                collinear_points = [opposite_vertices[0], altitude_foot, opposite_vertices[1]]

            elif version == "2":

                # Version 2: Collinear(DBC)

                collinear_points = [altitude_foot, opposite_vertices[0], opposite_vertices[1]]

            elif version == "3":

                # Version 3: Collinear(BCD)

                collinear_points = [opposite_vertices[0], opposite_vertices[1], altitude_foot]

            # If we don't already have this collinearity fact, add it to collinear_facts

            if collinear_points and not any(''.join(sorted(collinear_points)) == ''.join(sorted(fact))

                                            for fact in self.collinear_facts):
                self.collinear_facts.append(collinear_points)

                print(
                    f"Added collinearity constraint: {collinear_points[0]}{collinear_points[1]}{collinear_points[2]} are collinear")

            # Add right angle constraint

            angle_name = None

            if version == "1":

                # Version 1: Equal(MeasureOfAngle(BDA),90)

                angle_name = f"{opposite_vertices[0]}{altitude_foot}{altitude_vertex}"  # "BDA"

            elif version == "2":

                # Version 2: Equal(MeasureOfAngle(ADB),90)

                angle_name = f"{altitude_vertex}{altitude_foot}{opposite_vertices[0]}"  # "ADB"

            elif version == "3":

                # Version 3: Equal(MeasureOfAngle(CDA),90)

                angle_name = f"{opposite_vertices[1]}{altitude_foot}{altitude_vertex}"  # "CDA"

            if angle_name:
                angle_var = self.add_angle(angle_name[0], angle_name[1], angle_name[2])

                self.solver.add(angle_var == 90)

                print(f"Added right angle constraint: angle {angle_name} = 90°")

            print(f"Added altitude fact: {altitude_line} is an altitude of triangle {triangle} (version {version})")

            return None

        elif theorem_name == "round_angle":
            version = args[0]
            if version == "1":
                # Expected conclusion: "Equal(Add(MeasureOfAngle(FBC),MeasureOfAngle(CBF)),360)"
                match = re.search(
                    r'Equal\(Add\(MeasureOfAngle\((\w{3})\),MeasureOfAngle\((\w{3})\)\),360\)',
                    conclusions[0]
                )

                if match:
                    angle1, angle2 = match.groups()

                    # Get (or create) angle variables
                    angle1_var = self.add_angle(angle1[0], angle1[1], angle1[2])
                    angle2_var = self.add_angle(angle2[0], angle2[1], angle2[2])

                    # Add the constraint that the sum of angles equals 360 degrees
                    self.solver.add(angle1_var + angle2_var == 360)

                    print(f"Added round angle constraint: {angle1} + {angle2} = 360°")
                    return None
                else:
                    return GeometricError(
                        tier=ErrorTier.TIER1_THEOREM_CALL_SYNTAX_VIOLATION,
                        message="Conclusion format error for round_angle",
                        details=f"Expected pattern Equal(Add(MeasureOfAngle(XXX),MeasureOfAngle(YYY)),360) but got {conclusions[0]}"
                    )
            else:
                return GeometricError(
                    tier=ErrorTier.TIER1_THEOREM_CALL_SYNTAX_VIOLATION,
                    message=f"Unsupported version {version} for round_angle"
                )




        # Add this to the cosine_theorem handler in your adding_conclution method









        elif theorem_name == "flat_angle":
            version = args[0]
            if version == "1":
                # Expected conclusion: "Equal(MeasureOfAngle(BPA),180)"
                match = re.search(
                    r'Equal\(MeasureOfAngle\((\w{3})\),180\)',
                    conclusions[0]
                )

                if match:
                    angle_name = match.group(1)

                    # Get (or create) the angle variable
                    angle_var = self.add_angle(angle_name[0], angle_name[1], angle_name[2])

                    # Add the constraint that this is a straight/flat angle (180 degrees)
                    self.solver.add(angle_var == 180)

                    print(f"Added flat angle constraint: {angle_name} = 180°")
                    return None
                else:
                    return GeometricError(
                        tier=ErrorTier.TIER1_THEOREM_CALL_SYNTAX_VIOLATION,
                        message="Conclusion format error for flat_angle",
                        details=f"Expected pattern Equal(MeasureOfAngle(XXX),180) but got {conclusions[0]}"
                    )
            else:
                return GeometricError(
                    tier=ErrorTier.TIER1_THEOREM_CALL_SYNTAX_VIOLATION,
                    message=f"Unsupported version {version} for flat_angle"
                )




        elif theorem_name == "circle_property_circular_power_chord_and_chord":
            version = args[0]
            if version == "1":
                # Parse conclusion: "Equal(Mul(LengthOfLine(ED),LengthOfLine(EC)),Mul(LengthOfLine(EB),LengthOfLine(EA)))"
                match = re.search(
                    r'Equal\(Mul\(LengthOfLine\((\w+)\),LengthOfLine\((\w+)\)\),Mul\(LengthOfLine\((\w+)\),LengthOfLine\((\w+)\)\)\)',
                    conclusions[0]
                )

                if match:
                    segment1, segment2, segment3, segment4 = match.groups()

                    # Get (or create) length variables for the segments
                    length1 = self.add_length(segment1[0], segment1[1])
                    length2 = self.add_length(segment2[0], segment2[1])
                    length3 = self.add_length(segment3[0], segment3[1])
                    length4 = self.add_length(segment4[0], segment4[1])

                    # Add the power of circle constraint: ED × EC = EB × EA
                    self.solver.add(length1 * length2 == length3 * length4)

                    print(f"Added circle power constraint: {segment1} × {segment2} = {segment3} × {segment4}")
                    return None
                else:
                    return GeometricError(
                        tier=ErrorTier.TIER1_THEOREM_CALL_SYNTAX_VIOLATION,
                        message="Conclusion format error for circle_property_circular_power_chord_and_chord",
                        details=f"Expected pattern Equal(Mul(...),Mul(...)) but got {conclusions[0]}"
                    )
            else:
                return GeometricError(
                    tier=ErrorTier.TIER1_THEOREM_CALL_SYNTAX_VIOLATION,
                    message=f"Unsupported version {version} for circle_property_circular_power_chord_and_chord"
                )




        elif theorem_name == "altitude_of_quadrilateral_judgment_diagonal":

            version = args[0].strip()

            if version not in {"1", "2"}:
                return GeometricError(

                    tier=ErrorTier.TIER1_THEOREM_CALL_SYNTAX_VIOLATION,

                    message=f"Unsupported version {version} for altitude_of_quadrilateral_judgment_diagonal",

                    details="Supported versions are 1 and 2"

                )

            quad = args[1].strip()  # e.g., "ABCD"

            # Determine the diagonal based on version

            diagonal = None

            if version == "1":

                diagonal = f"{quad[0]}{quad[2]}"  # AC

            elif version == "2":

                diagonal = f"{quad[3]}{quad[1]}"  # DB

            # Expected conclusion format

            expected_conclusion = f"IsAltitudeOfQuadrilateral({diagonal},{quad})"

            # Verify conclusion matches expected format

            altitude_match = re.search(r'IsAltitudeOfQuadrilateral\((\w+),(\w+)\)', conclusions[0])

            if not altitude_match:
                return GeometricError(

                    tier=ErrorTier.TIER1_THEOREM_CALL_SYNTAX_VIOLATION,

                    message="Invalid conclusion format for altitude_of_quadrilateral_judgment_diagonal",

                    details=f"Expected format: {expected_conclusion}"

                )

            line = altitude_match.group(1)  # First capture group (e.g., AC or DB)

            conclusion_quad = altitude_match.group(2)  # Second capture group (e.g., ABCD)

            # Verify conclusion matches expected values

            if line != diagonal or conclusion_quad != quad:
                return GeometricError(

                    tier=ErrorTier.TIER1_THEOREM_CALL_SYNTAX_VIOLATION,

                    message="Conclusion doesn't match expected values",

                    details=f"Expected {expected_conclusion}, got IsAltitudeOfQuadrilateral({line},{conclusion_quad})"

                )

            # Initialize the altitudes structure if needed

            if not hasattr(self, 'altitudes'):
                self.altitudes = {}

            # Store the altitude information

            if quad not in self.altitudes:
                self.altitudes[quad] = []

            self.altitudes[quad].append(line)

            # Create a height variable for this quad and link it to the altitude length

            if not hasattr(self, 'quad_heights'):
                self.quad_heights = {}

            if quad not in self.quad_heights:
                height_var = Real(f"heightQuadr_{quad}")

                self.quad_heights[quad] = height_var

                self.solver.add(height_var >= 0)

            # Set the height equal to the length of the altitude line

            altitude_length = self.add_length(line[0], line[1])

            self.solver.add(self.quad_heights[quad] == altitude_length)

            # Add right angle constraint

            if version == "1":

                # Version 1: Equal(MeasureOfAngle(BCA),90)

                angle_name = f"{quad[1]}{quad[2]}{quad[0]}"  # BCA

            elif version == "2":

                # Version 2: Equal(MeasureOfAngle(DBC),90)

                angle_name = f"{quad[3]}{quad[1]}{quad[2]}"  # DBC

            angle_var = self.add_angle(angle_name[0], angle_name[1], angle_name[2])

            self.solver.add(angle_var == 90)

            print(f"Added altitude fact for version {version}: {line} is an altitude of {quad}")

            print(f"Added right angle constraint: angle {angle_name} = 90°")

            print(f"Set quadrilateral height: {quad} height = {line}")

            return None



        elif theorem_name == "perpendicular_bisector_judgment_distance_equal":

            match = re.search(r'IsPerpendicularBisectorOfLine\((\w+),(\w+)\)', conclusions[0])

            if not match:
                return GeometricError(

                    tier=ErrorTier.TIER1_THEOREM_CALL_SYNTAX_VIOLATION,

                    message="Invalid conclusion format for perpendicular_bisector_judgment_distance_equal"

                )

            bisector, bisected = match.groups()  # e.g. "BD", "CA"

            # Find point D from the collinear fact ADC

            bisector_point = None  # This will be point D

            for fact in self.collinear_facts:

                fact_str = ''.join(fact)

                for point in bisector:

                    if point in fact_str and all(p in fact_str for p in bisected):
                        bisector_point = point

                        break

                if bisector_point:
                    break

            if not bisector_point:
                return GeometricError(

                    tier=ErrorTier.TIER1_THEOREM_CALL_SYNTAX_VIOLATION,

                    message="Could not find bisector point on the bisected line",

                    details=f"Need collinear fact containing point from {bisector} and points {bisected}"

                )

            # Get the two parts of the bisected line

            parts = [p for p in bisected]

            # Add equal distance constraints for the two parts

            # If bisected is CA and bisector_point is D, this adds CD = DA

            dist1 = self.add_length(bisector_point, parts[0])

            dist2 = self.add_length(bisector_point, parts[1])

            self.solver.add(dist1 == dist2)

            # Add right angle constraints

            # If bisector is BD, get the B point

            other_point = next(p for p in bisector if p != bisector_point)

            # Get collinear points for D (intersecting point)

            collinear_points = None

            for fact in self.collinear_facts:

                if bisector_point in fact:
                    collinear_points = fact

                    break

            if collinear_points:

                # Add right angle for both points on the collinear line

                for p in collinear_points:

                    if p != bisector_point:  # For each endpoint (C and A)

                        angle = self.add_angle(other_point, bisector_point, p)  # BDC and BDA

                        self.solver.add(angle == 90)

                        print(f"Added 90° angle constraint for ∠{other_point}{bisector_point}{p}")

            print(
                f"Added perpendicular bisector constraints: {bisector_point} divides {bisected} equally with right angles")

            return None






        # This code should replace the altitude handling in your adding_conclution method

        # for the altitude_of_quadrilateral_judgment_left_vertex theorem:

        elif theorem_name == "altitude_of_quadrilateral_judgment_left_vertex":

            version = args[0].strip()

            if version not in {"1", "2", "3"}:
                return GeometricError(

                    tier=ErrorTier.TIER1_THEOREM_CALL_SYNTAX_VIOLATION,

                    message=f"Unsupported version {version} for altitude_of_quadrilateral_judgment_left_vertex",

                    details="Supported versions are 1, 2, and 3"

                )

            altitude_line = args[1].strip()  # e.g., "AF"

            quad_name = args[2].strip()  # e.g., "ABCD"

            # Expected conclusion format

            altitude_fact = f"IsAltitudeOfQuadrilateral({altitude_line},{quad_name})"

            # Initialize the altitudes collection appropriately

            if not hasattr(self, 'altitudes'):

                self.altitudes = set()

            elif isinstance(self.altitudes, dict):  # Handle potential conversion from dict to set

                self.altitudes = set(self.altitudes.keys())

            # Record the altitude fact

            self.altitudes.add(altitude_fact)

            # Set up the height variable in quad_heights if that collection exists

            if hasattr(self, 'quad_heights'):
                height_var = self.add_length(altitude_line[0], altitude_line[1])

                self.quad_heights[quad_name] = height_var

                print(f"Set quadrilateral height: {quad_name} height = {altitude_line}")

            # Set up the right angle constraint based on version

            if version == "1":

                # Version 1: Equal(MeasureOfAngle(BFA),90)

                point_B = quad_name[1]  # Second vertex

                point_F = altitude_line[1]  # Second point of altitude

                point_A = altitude_line[0]  # First point of altitude

                angle_var = self.add_angle(point_B, point_F, point_A)

                self.solver.add(angle_var == 90)

                print(f"Added right angle constraint for version 1: angle({point_B}{point_F}{point_A}) = 90°")


            elif version == "2":

                # Version 2: Equal(MeasureOfAngle(AFB),90)

                point_A = altitude_line[0]  # First point of altitude

                point_F = altitude_line[1]  # Second point of altitude

                point_B = quad_name[1]  # Second vertex

                angle_var = self.add_angle(point_A, point_F, point_B)

                self.solver.add(angle_var == 90)

                print(f"Added right angle constraint for version 2: angle({point_A}{point_F}{point_B}) = 90°")


            elif version == "3":

                # Version 3: Equal(MeasureOfAngle(CFA),90)

                point_C = quad_name[2]  # Third vertex

                point_F = altitude_line[1]  # Second point of altitude

                point_A = altitude_line[0]  # First point of altitude

                angle_var = self.add_angle(point_C, point_F, point_A)

                self.solver.add(angle_var == 90)

                print(f"Added right angle constraint for version 3: angle({point_C}{point_F}{point_A}) = 90°")

            # Add a collinearity constraint for the foot of the altitude

            collinear_points = None

            if version == "1":

                # Version 1: Collinear(BFC)

                collinear_points = [quad_name[1], altitude_line[1], quad_name[2]]

            elif version == "2":

                # Version 2: Collinear(FBC)

                collinear_points = [altitude_line[1], quad_name[1], quad_name[2]]

            elif version == "3":

                # Version 3: Collinear(BCF)

                collinear_points = [quad_name[1], quad_name[2], altitude_line[1]]

            # If we don't already have this collinearity fact, add it to collinear_facts

            if collinear_points and not any(''.join(collinear_points) == ''.join(fact)

                                            or ''.join(collinear_points) == ''.join(fact[::-1])

                                            for fact in self.collinear_facts):
                self.collinear_facts.append(collinear_points)

                print(
                    f"Added collinearity constraint: {collinear_points[0]}{collinear_points[1]}{collinear_points[2]} are collinear")

            print(f"Recorded altitude fact: {altitude_fact}")

            return None


        elif theorem_name == "parallelogram_property_opposite_line_equal":
            # Expected conclusion: "Equal(LengthOfLine(DC),LengthOfLine(BA))"
            match = re.search(r'Equal\(LengthOfLine\((\w+)\),LengthOfLine\((\w+)\)\)', conclusions[0])
            if match:
                line1, line2 = match.groups()
                var1 = self.add_length(line1[0], line1[1])
                var2 = self.add_length(line2[0], line2[1])
                self.solver.add(var1 == var2)
                print(f"Added constraint: LengthOfLine({line1}) == LengthOfLine({line2})")
                return None
            else:
                return GeometricError(
                    tier=ErrorTier.TIER1_THEOREM_CALL_SYNTAX_VIOLATION,
                    message="Conclusion format error for parallelogram_property_opposite_line_equal."
                )


        elif theorem_name == "parallelogram_area_formula_common":

            # Expected conclusion: "Equal(AreaOfQuadrilateral(ACDB),Mul(HeightOfQuadrilateral(ACDB),LengthOfLine(CD)))"

            match = re.search(

                r'Equal\(AreaOfQuadrilateral\((\w+)\),Mul\(HeightOfQuadrilateral\(\1\),LengthOfLine\((\w+)\)\)\)',

                conclusions[0])

            if match:

                quad, base_line = match.groups()

                # Check that we have a height for this quad

                if quad not in self.quad_heights:
                    return GeometricError(

                        tier=ErrorTier.TIER2_PREMISE_VIOLATION,

                        message=f"No height established for quadrilateral {quad}",

                        details="Height must be established through an altitude theorem first"

                    )

                # Get or create area variable

                if quad not in self.quad_areas:
                    self.quad_areas[quad] = Real(f"AreaOfQuadrilateral_{quad}")

                    self.solver.add(self.quad_areas[quad] >= 0)

                area_var = self.quad_areas[quad]

                # Get the height variable we previously stored

                height_var = self.quad_heights[quad]

                # Get the base length

                base_var = self.add_length(base_line[0], base_line[1])

                # Add the area formula constraint

                self.solver.add(area_var == height_var * base_var)

                print(
                    f"Added parallelogram area constraint: AreaOfQuadrilateral({quad}) == HeightOfQuadrilateral({quad}) * LengthOfLine({base_line})")

                return None

            else:

                return GeometricError(

                    tier=ErrorTier.TIER1_THEOREM_CALL_SYNTAX_VIOLATION,

                    message="Conclusion format error for parallelogram_area_formula_common."

                )




        elif theorem_name == "isosceles_triangle_judgment_line_equal":
            # Expected theorem call: isosceles_triangle_judgment_line_equal(1, T)
            # where T is the triangle name (e.g., "JPN").
            tri = args[1].strip()

            # To record that the triangle is isosceles, add T and all its cyclic rotations
            # to an attribute (e.g. self.isosceles_triangles).
            def cyclic_rotations(s):
                rotations = set()
                for i in range(len(s)):
                    rotations.add(s[i:] + s[:i])
                return rotations

            rotations = cyclic_rotations(tri)
            if not hasattr(self, "isosceles_triangles"):
                self.isosceles_triangles = set()
            self.isosceles_triangles.update(rotations)
            print(f"Recorded isosceles triangle: {tri} and its rotations {rotations}")
            return None




        elif theorem_name == "isosceles_triangle_property_angle_equal":

            version = args[0]

            if version == "1":

                # Parse the conclusion to extract the angle equality

                match = re.search(r'Equal\(MeasureOfAngle\((\w{3})\),MeasureOfAngle\((\w{3})\)\)', conclusions[0])

                if not match:
                    return GeometricError(

                        tier=ErrorTier.TIER1_THEOREM_CALL_SYNTAX_VIOLATION,

                        message="Conclusion format error for isosceles_triangle_property_angle_equal",

                        details=f"Expected Equal(MeasureOfAngle(...),MeasureOfAngle(...)) pattern but got {conclusions[0]}"

                    )

                angle1, angle2 = match.groups()  # e.g., "ABC" and "BCA"

                # Add constraint that the angles are equal

                angle1_var = self.add_angle(angle1[0], angle1[1], angle1[2])

                angle2_var = self.add_angle(angle2[0], angle2[1], angle2[2])

                self.solver.add(angle1_var == angle2_var)

                print(
                    f"Added angle equality for isosceles triangle: MeasureOfAngle({angle1}) = MeasureOfAngle({angle2})")

                return None

            else:

                return GeometricError(

                    tier=ErrorTier.TIER1_THEOREM_CALL_SYNTAX_VIOLATION,

                    message=f"Unsupported version {version} for isosceles_triangle_property_angle_equal",

                    details="Only version 1 is supported"

                )


        elif theorem_name == "arc_length_formula":
            # Expected conclusion, for example:
            # "Equal(LengthOfArc(PSR),Mul(MeasureOfArc(PSR),1/180*pi,RadiusOfCircle(P)))"
            # We use a regex to extract:
            #   - the arc token (e.g. "PSR")
            #   - the multiplier expression (e.g. "1/180*pi")
            #   - the circle identifier (e.g. "P")
            pattern = r'Equal\(LengthOfArc\((\w+)\),Mul\(MeasureOfArc\(\1\),([^,]+),RadiusOfCircle\((\w+)\)\)\)'
            m = re.match(pattern, conclusions[0])
            if m:
                arc_token, factor_expr, circle_id = m.groups()
                # Create a new variable for the arc's length using a naming convention:
                length_var_name = f"lengthArc_{self.normalize_arc(arc_token)}"
                length_arc_var = Real(length_var_name)
                # Retrieve the arc measure variable (stored in self.arcs) using your helper:
                arc_measure = self.add_arc(arc_token)
                try:
                    factor_value = float(eval(factor_expr, {"pi": 3.141592653589793}))
                except Exception as e:
                    return GeometricError(
                        tier=ErrorTier.TIER1_THEOREM_CALL_SYNTAX_VIOLATION,
                        message="Error evaluating multiplier expression in arc_length_formula",
                        details=str(e)
                    )
                # Get (or create) the radius of the circle:
                if circle_id in self.circle_radii:
                    radius_var = self.circle_radii[circle_id]
                else:
                    radius_var = Real(f"radius_{circle_id}")
                    self.circle_radii[circle_id] = radius_var
                    self.solver.add(radius_var >= 0)
                # Add the constraint:
                # LengthOfArc = MeasureOfArc * factor_value * RadiusOfCircle
                self.solver.add(length_arc_var == arc_measure * factor_value * radius_var)
                print(
                    f"Added arc length constraint: {length_var_name} = {arc_measure} * {factor_value} * RadiusOfCircle({circle_id})")
            else:
                return GeometricError(
                    tier=ErrorTier.TIER1_THEOREM_CALL_SYNTAX_VIOLATION,
                    message="Conclusion format error for arc_length_formula",
                    details=f"Expected pattern not found in: {conclusions[0]}"
                )

        elif theorem_name == "circle_property_circular_power_segment_and_segment_line":
            # Expected arguments: version, token1, token2, token3.
            # For example: (1, "AFB", "AGC", "E")
            token1 = args[1].strip()  # e.g., "AFB"
            token2 = args[2].strip()  # e.g., "AGC"
            # token3 (the center "E") is used in the premise but not directly in the conclusion.
            # Interpret token1 = "AFB" as: A, F, B.
            # Then we add the constraint:
            #   (LengthOfLine(AF) * LengthOfLine(AB)) = (LengthOfLine(AG) * LengthOfLine(AC))
            af_var = self.add_length(token1[0], token1[1])  # AF
            ab_var = self.add_length(token1[0], token1[2])  # AB
            # Similarly, for token2 = "AGC" as: A, G, C.
            ag_var = self.add_length(token2[0], token2[1])  # AG
            ac_var = self.add_length(token2[0], token2[2])  # AC
            self.solver.add(af_var * ab_var == ag_var * ac_var)
            print(
                f"Added power-of-a-circle constraint: (LengthOfLine({token1[0]}{token1[1]}) * LengthOfLine({token1[0]}{token1[2]})) = (LengthOfLine({token2[0]}{token2[1]}) * LengthOfLine({token2[0]}{token2[2]}))")
            return None


        elif theorem_name == "circle_property_circular_power_tangent_and_segment_line":
            # Expected arguments: version, token1, token2, token3
            # For example: (1, "DC", "DBF", "E")
            token1 = args[1].strip()  # e.g., "DC"
            token2 = args[2].strip()  # e.g., "DBF"
            # We'll assume token2 has exactly three characters (e.g., "DBF")
            # so that:
            #   external segment = LengthOfLine(DB)  [from token2[0] and token2[1]]
            #   entire secant   = LengthOfLine(DF)  [from token2[0] and token2[2]]
            tangent_var = self.add_length(token1[0], token1[1])  # LengthOfLine(DC)
            external_var = self.add_length(token2[0], token2[1])  # LengthOfLine(DB)
            secant_var = self.add_length(token2[0], token2[2])  # LengthOfLine(DF)
            self.solver.add(tangent_var * tangent_var == external_var * secant_var)
            print(
                f"Added tangent–secant constraint: (LengthOfLine({token1}))² = LengthOfLine({token2[0:2]}) * LengthOfLine({token2[0]}{token2[2]})")
            return None



        elif theorem_name == "rectangle_property_diagonal_equal":
            # Expected argument: the rectangle name (e.g., "PNML")
            if len(args) < 2:
                return GeometricError(
                    tier=ErrorTier.TIER1_THEOREM_CALL_SYNTAX_VIOLATION,
                    message="Missing rectangle name for rectangle_property_diagonal_equal."
                )
            rect = args[1].strip()  # e.g., "PNML"
            if len(rect) < 4:
                return GeometricError(
                    tier=ErrorTier.TIER1_THEOREM_CALL_SYNTAX_VIOLATION,
                    message=f"Rectangle name {rect} is invalid (expected at least 4 letters)."
                )
            # For a rectangle with vertices in cyclic order, the diagonals are:
            #   diag1: from the first vertex to the third, and
            #   diag2: from the second vertex to the fourth.
            diag1 = rect[0] + rect[2]  # e.g., if rect="PNML", diag1 = "PM"
            diag2 = rect[1] + rect[3]  # e.g., diag2 = "NL"
            # Retrieve or create the corresponding length variables.
            var1 = self.add_length(diag1[0], diag1[1])
            var2 = self.add_length(diag2[0], diag2[1])
            # Add the equality constraint.
            self.solver.add(var1 == var2)
            print(f"Added rectangle diagonal equality: LengthOfLine({diag1}) == LengthOfLine({diag2})")
            return None




        elif theorem_name == "parallelogram_property_diagonal_bisection":
            # Expected theorem call: parallelogram_property_diagonal_bisection(1, PNML, J)
            # The intended conclusion is to record that J is the midpoint of the diagonal joining
            # the 1st and 3rd vertices of PNML.
            # In other words, if the diagonal is from P to M (where para_name="PNML"),
            # then we add the constraint: LengthOfLine(PJ) == LengthOfLine(JM).
            if len(args) < 3:
                return GeometricError(
                    tier=ErrorTier.TIER1_THEOREM_CALL_SYNTAX_VIOLATION,
                    message="Insufficient arguments for parallelogram_property_diagonal_bisection."
                )
            para_name = args[1].strip()  # e.g., "PNML"
            mid_candidate = args[2].strip()  # e.g., "J"

            # Compute the first diagonal from the parallelogram: vertices 1 and 3.
            diag = para_name[0] + para_name[2]  # e.g., for "PNML", diag = "PM"
            # To state that mid_candidate J is the midpoint of the diagonal, we require:
            #   LengthOfLine(PJ) = LengthOfLine(JM)
            first_half = self.add_length(para_name[0], mid_candidate)
            second_half = self.add_length(mid_candidate, para_name[2])
            self.solver.add(first_half == second_half)
            print(
                f"Added diagonal bisection: {mid_candidate} is the midpoint of {diag} (LengthOfLine({para_name[0]}{mid_candidate}) == LengthOfLine({mid_candidate}{para_name[2]}))")
            return None







        elif theorem_name == "parallel_property_collinear_extend":

            version = args[0].strip()

            if version not in {"1", "2", "3"}:  # Updated to include version "2"

                return GeometricError(

                    tier=ErrorTier.TIER1_THEOREM_CALL_SYNTAX_VIOLATION,

                    message=f"Unsupported version {version} for parallel_property_collinear_extend.",

                    details=f"Version provided: {version}"

                )

            token1 = args[1].strip()  # e.g., "GA"

            token2 = args[2].strip()  # e.g., "HD"

            token3 = args[3].strip()  # e.g., "J"

            # Helper function to add all variations for a given line pair.

            def add_parallel_variations(line_tuple):

                a, b = line_tuple

                variations = {

                    (a, b),

                    (b, a),

                    (a[::-1], b),

                    (a, b[::-1]),

                    (a[::-1], b[::-1]),

                    (b[::-1], a[::-1]),

                    (b, a[::-1]),

                    (b[::-1], a)

                }

                for var in variations:
                    self.parallel_pairs.add(var)

            # For the conclusion, form the new parallel lines based on the version.

            if version == "1":

                # For version 1: token3 + token1[0] and token3 + token1[1]

                new_line1 = token3 + token1[0]  # e.g., "JG"

                new_line2 = token3 + token1[1]  # e.g., "JA"

            elif version == "2":

                # For version 2: token1[0] + token3 and token1[1] + token3

                new_line1 = token1[0] + token3  # e.g., "AM"

                new_line2 = token1[1] + token3  # e.g., "BM"

            elif version == "3":

                # For version 3: token1[0] + token3 and token3 + token1[1]

                new_line1 = token1[0] + token3  # e.g., "GJ"

                new_line2 = token3 + token1[1]  # e.g., "JA"

            # Add parallel variations with token2.

            add_parallel_variations((new_line1, token2))

            add_parallel_variations((new_line2, token2))

            print(
                f"[Version {version}] Added parallel extension with new lines: {new_line1} and {new_line2} parallel to {token2}")

            return None







        elif theorem_name == "circle_property_circular_power_segment_and_segment_angle":
            # Expected conclusion: Equal(Sub(MeasureOfArc(BVT),MeasureOfArc(BSU)),Mul(MeasureOfAngle(SRU),2))
            # Use regex to extract the pieces:
            pattern = r'Equal\(Sub\(MeasureOfArc\((\w+)\),MeasureOfArc\((\w+)\)\),Mul\(MeasureOfAngle\((\w+)\),([\d/\.]+)\)\)'
            m = re.match(pattern, conclusions[0])
            if m:
                arc1, arc2, angle_str, factor_str = m.groups()
                arc1_var = self.add_arc(arc1)  # e.g. BVT
                arc2_var = self.add_arc(arc2)  # e.g. BSU
                angle_var = self.add_angle(angle_str[0], angle_str[1], angle_str[2])
                try:
                    factor_val = float(eval(factor_str))
                except Exception:
                    factor_val = 2.0
                # Add the constraint: (arc1 - arc2) == factor * angle
                self.solver.add(arc1_var - arc2_var == factor_val * angle_var)
                print(
                    f"Added constraint: (MeasureOfArc({arc1}) - MeasureOfArc({arc2})) == {factor_val} * MeasureOfAngle({angle_str})")
            else:
                return GeometricError(
                    tier=ErrorTier.TIER1_THEOREM_CALL_SYNTAX_VIOLATION,
                    message="Conclusion format error for circle_property_circular_power_segment_and_segment_angle",
                    details=f"Expected pattern not found in: {conclusions[0]}"
                )



        elif theorem_name == "midsegment_of_triangle_judgment_parallel":

            version = args[0]

            if version not in {"1", "2", "3"}:
                return GeometricError(

                    tier=ErrorTier.TIER1_THEOREM_CALL_SYNTAX_VIOLATION,

                    message=f"Unsupported version {version} for midsegment_of_triangle_judgment_parallel",

                    details="Supported versions are 1, 2, and 3"

                )

            if len(args) < 3:
                return GeometricError(

                    tier=ErrorTier.TIER1_THEOREM_CALL_SYNTAX_VIOLATION,

                    message="Insufficient arguments for midsegment_of_triangle_judgment_parallel",

                    details="Expected: midsegment_of_triangle_judgment_parallel(version, line, triangle)"

                )

            midseg_line = args[1].strip()

            triangle_token = args[2].strip()

            if len(midseg_line) != 2 or len(triangle_token) != 3:
                return GeometricError(

                    tier=ErrorTier.TIER1_THEOREM_CALL_SYNTAX_VIOLATION,

                    message=f"Invalid input format for midsegment/triangle: '{midseg_line}', '{triangle_token}'",

                    details="Midsegment must have 2 points, triangle must have 3."

                )

            # Expected conclusion: ["IsMidsegmentOfTriangle(DE,ABC)"]

            m = re.search(r'IsMidsegmentOfTriangle\((\w+),(\w+)\)', conclusions[0])

            if m:

                conclusion_line, conclusion_triangle = m.groups()

                # Basic check: conclusion tokens must match theorem call arguments

                if conclusion_line != midseg_line or conclusion_triangle != triangle_token:
                    return GeometricError(

                        tier=ErrorTier.TIER1_THEOREM_CALL_SYNTAX_VIOLATION,

                        message=f"Conclusion does not match expected tokens for midsegment_of_triangle_judgment_parallel",

                        details=f"Expected IsMidsegmentOfTriangle({midseg_line},{triangle_token}), got IsMidsegmentOfTriangle({conclusion_line},{conclusion_triangle})"

                    )

                # Record this midsegment fact (useful for other property theorems)

                if not hasattr(self, "midsegments"):
                    self.midsegments = set()

                # Ensure midsegment_fact uses the *exact* strings from the conclusion/call

                midsegment_fact = ("IsMidsegmentOfTriangle", (midseg_line, triangle_token))

                self.midsegments.add(midsegment_fact)

                print(
                    f"[Version {version}] Added midsegment judgment: IsMidsegmentOfTriangle({midseg_line},{triangle_token})")

                # --- GENERALIZED LOGIC: Add implied Z3 constraints ---

                # The conclusion IsMidsegmentOfTriangle(DE, ABC) implies:

                # 1. D is midpoint of one side (e.g., AB) -> AD = DB

                # 2. E is midpoint of another side (e.g., AC) -> AE = EC

                # 3. DE is parallel to the third side (e.g., BC)

                # 4. Length(DE) = 1/2 * Length(third side)

                # Identify vertices and midsegment endpoints

                p1, p2 = midseg_line[0], midseg_line[1]

                v1, v2, v3 = triangle_token[0], triangle_token[1], triangle_token[2]

                triangle_vertices = {v1, v2, v3}

                midseg_endpoints_set = {p1, p2}

                midpoint1_info = None  # Will store {'midpoint': char, 'side': (char, char), 'collinear_fact': list}

                midpoint2_info = None

                processed_midpoints = set()

                # Find which sides p1 and p2 are midpoints of using COLLINEAR facts

                # A collinear fact like Collinear(AXB) implies X could be midpoint of AB

                print(
                    f"Attempting to find midpoint sides for {midseg_line} in {triangle_token} using collinear facts: {self.collinear_facts}")

                for fact_points in self.collinear_facts:

                    fact_set = set(fact_points)

                    common_triangle_vertices = fact_set.intersection(triangle_vertices)

                    common_midseg_endpoints = fact_set.intersection(midseg_endpoints_set)

                    # A valid collinear fact for a side containing a midpoint should have:

                    # - Exactly 2 triangle vertices (the side endpoints)

                    # - Exactly 1 midsegment endpoint (the midpoint, which hasn't been processed yet)

                    # - Exactly 3 points in total (endpoint1, midpoint, endpoint2)

                    if len(fact_points) == 3 and len(common_triangle_vertices) == 2 and len(
                            common_midseg_endpoints) == 1:

                        midpoint = list(common_midseg_endpoints)[0]

                        side_vertices = tuple(
                            sorted(list(common_triangle_vertices)))  # Ensure consistent order (v1, v2)

                        if midpoint == p1 and p1 not in processed_midpoints:

                            midpoint1_info = {'midpoint': p1, 'side': side_vertices, 'collinear_fact': fact_points}

                            processed_midpoints.add(p1)

                            print(
                                f"  Identified {p1} as potential midpoint of side {side_vertices} based on Collinear({fact_points})")

                        elif midpoint == p2 and p2 not in processed_midpoints:

                            midpoint2_info = {'midpoint': p2, 'side': side_vertices, 'collinear_fact': fact_points}

                            processed_midpoints.add(p2)

                            print(
                                f"  Identified {p2} as potential midpoint of side {side_vertices} based on Collinear({fact_points})")

                    # Stop if we've found both distinct midpoints

                    if midpoint1_info and midpoint2_info:
                        break

                # Check if we successfully identified both midpoints and their sides

                if not midpoint1_info or not midpoint2_info:
                    print(
                        f"WARNING: Could not reliably determine BOTH midpoint sides for midsegment {midseg_line} in {triangle_token} using collinear facts. Skipping implied constraints.")

                    # Optionally return an error instead of just warning:

                    # return GeometricError(

                    #     tier=ErrorTier.TIER2_PREMISE_VIOLATION, # Or maybe TIER1 if conclusion implies this info MUST be derivable

                    #     message=f"Cannot determine which sides {p1} and {p2} are midpoints of in {triangle_token}",

                    #     details=f"Check collinear facts involving {p1}, {p2} and vertices {v1},{v2},{v3}. Found midpoints: {midpoint1_info}, {midpoint2_info}"

                    # )

                    return None  # Proceed without adding potentially incorrect constraints

                # Extract identified info

                mp1 = midpoint1_info['midpoint']

                side1_v1, side1_v2 = midpoint1_info['side']

                mp2 = midpoint2_info['midpoint']

                side2_v1, side2_v2 = midpoint2_info['side']

                # Verify the two sides identified are different

                if set(midpoint1_info['side']) == set(midpoint2_info['side']):
                    print(
                        f"ERROR: Both identified midpoints {mp1} and {mp2} seem to belong to the same side {midpoint1_info['side']}. Skipping constraints.")

                    return None  # Cannot proceed if both midpoints are on the same side

                # Identify the third side (vertices not part of the two sides found)

                involved_vertices = {side1_v1, side1_v2, side2_v1, side2_v2}  # Should contain 3 unique vertices

                third_side_endpoints = tuple(sorted(list(triangle_vertices - involved_vertices)))

                # The third side should consist of the two triangle vertices that are NOT endpoints of the midsegment sides' common vertex

                # Example: Midpoints D on AB, E on AC. Involved = A,B,A,C -> {A,B,C}. Third side is BC.

                # Example: Midpoints H on CF, D on CB. Involved = C,F,C,B -> {C,F,B}. Third side is FB.

                common_vertex = list(set(midpoint1_info['side']).intersection(set(midpoint2_info['side'])))

                if len(common_vertex) != 1:
                    print(
                        f"ERROR: Sides {midpoint1_info['side']} and {midpoint2_info['side']} do not share exactly one vertex. Cannot determine third side.")

                    return None

                third_side_endpoints = tuple(sorted(list(involved_vertices - set(common_vertex))))

                if len(third_side_endpoints) != 2:
                    print(
                        f"ERROR: Could not determine third side for midsegment {midseg_line} in {triangle_token}. Involved vertices: {involved_vertices}, Common: {common_vertex}")

                    return None

                # --- Add Z3 Constraints ---

                # 1. Midpoint Equality Constraints

                len1a = self.add_length(side1_v1, mp1)

                len1b = self.add_length(mp1, side1_v2)

                self.solver.add(len1a == len1b)

                print(f"Added midsegment midpoint constraint: Length({side1_v1}{mp1}) == Length({mp1}{side1_v2})")

                len2a = self.add_length(side2_v1, mp2)

                len2b = self.add_length(mp2, side2_v2)

                self.solver.add(len2a == len2b)

                print(f"Added midsegment midpoint constraint: Length({side2_v1}{mp2}) == Length({mp2}{side2_v2})")

                # 2. Length Constraint (Midsegment = 1/2 * Third Side)

                third_side_line = "".join(third_side_endpoints)

                third_side_v1, third_side_v2 = third_side_endpoints

                third_side_var = self.add_length(third_side_v1, third_side_v2)

                midseg_var = self.add_length(p1, p2)

                from fractions import Fraction

                self.solver.add(midseg_var == third_side_var * Fraction(1, 2))

                # self.solver.add(2 * midseg_var == third_side_var) # Alternative form

                print(f"Added midsegment length constraint: Length({midseg_line}) == 1/2 * Length({third_side_line})")

                # 3. Parallel Constraint

                norm_midseg = self.normalize_line_name(midseg_line)

                norm_third = self.normalize_line_name(third_side_line)

                parallel_pair_normalized = tuple(sorted((norm_midseg, norm_third)))

                is_already_parallel = False

                for pair_str1, pair_str2 in self.parallel_pairs:

                    norm_existing_pair = tuple(
                        sorted((self.normalize_line_name(pair_str1), self.normalize_line_name(pair_str2))))

                    if norm_existing_pair == parallel_pair_normalized:
                        is_already_parallel = True

                        break

                if not is_already_parallel:
                    # Add the normalized pair and its reverse to self.parallel_pairs

                    self.parallel_pairs.add(parallel_pair_normalized)

                    self.parallel_pairs.add((parallel_pair_normalized[1], parallel_pair_normalized[0]))

                    # Also add the original string versions for potential lookup consistency

                    self.parallel_pairs.add(tuple(sorted((midseg_line, third_side_line))))

                    self.parallel_pairs.add(tuple(sorted((third_side_line, midseg_line))))

                    print(f"Added midsegment parallel constraint: {midseg_line} || {third_side_line}")

                # Ensure the midpoints are marked correctly in the midpoints dictionary if used elsewhere

                if not hasattr(self, "midpoints"):
                    self.midpoints = {}

                self.midpoints[midpoint1_info['side']] = mp1

                self.midpoints[tuple(reversed(midpoint1_info['side']))] = mp1

                self.midpoints[midpoint2_info['side']] = mp2

                self.midpoints[tuple(reversed(midpoint2_info['side']))] = mp2

                print(
                    f"Updated midpoints dictionary: {mp1} for {midpoint1_info['side']}, {mp2} for {midpoint2_info['side']}")

                return None  # Success


            else:

                # If conclusion parsing fails

                return GeometricError(

                    tier=ErrorTier.TIER1_THEOREM_CALL_SYNTAX_VIOLATION,

                    message="Conclusion format error for midsegment_of_triangle_judgment_parallel",

                    details=f"Expected format: IsMidsegmentOfTriangle({midseg_line},{triangle_token}) but got {conclusions[0]}"

                )




        elif theorem_name == "arc_property_circumference_angle_internal":
            # Expected conclusion:
            # Equal(MeasureOfAngle(BCD),Sub(180,Mul(MeasureOfArc(OBD),1/2)))
            #
            # We'll extract:
            #   - the inscribed angle token (e.g. "BCD")
            #   - the arc token (e.g. "OBD")
            #   - the factor expression (e.g. "1/2")
            pattern = r'Equal\(MeasureOfAngle\((\w{3})\),Sub\(180,Mul\(MeasureOfArc\((\w+)\),([^,)]+)\)\)\)'
            m = re.match(pattern, conclusions[0])
            if m:
                angle_token, arc_token, factor_expr = m.groups()
                # Get the angle variable (using your helper, which normalizes the three-letter string)
                angle_var = self.add_angle(angle_token[0], angle_token[1], angle_token[2])
                # Get the arc measure variable (using your add_arc method)
                arc_var = self.add_arc(arc_token)
                try:
                    factor_value = float(eval(factor_expr, {"pi": 3.141592653589793}))
                except Exception as e:
                    return GeometricError(
                        tier=ErrorTier.TIER1_THEOREM_CALL_SYNTAX_VIOLATION,
                        message="Error evaluating multiplier expression in arc_property_circumference_angle_internal",
                        details=str(e)
                    )
                # Add the constraint:
                #   MeasureOfAngle(angle_token) = 180 - (factor_value * MeasureOfArc(arc_token))
                self.solver.add(angle_var == 180 - (arc_var * factor_value))
                print(
                    f"Added arc circumference internal angle constraint: MeasureOfAngle({angle_token}) = 180 - {factor_value} * MeasureOfArc({arc_token})")
            else:
                return GeometricError(
                    tier=ErrorTier.TIER1_THEOREM_CALL_SYNTAX_VIOLATION,
                    message="Conclusion format error for arc_property_circumference_angle_internal",
                    details=f"Expected pattern not found in: {conclusions[0]}"
                )








        elif theorem_name == "circle_property_chord_perpendicular_bisect_chord":

            version = args[0].strip()

            if version not in {"1", "2"}:
                return GeometricError(

                    tier=ErrorTier.TIER1_THEOREM_CALL_SYNTAX_VIOLATION,

                    message=f"Unsupported version {version} for circle_property_chord_perpendicular_bisect_chord",

                    details="Supported versions are 1 and 2"

                )

            if len(args) < 4:
                return GeometricError(

                    tier=ErrorTier.TIER1_THEOREM_CALL_SYNTAX_VIOLATION,

                    message="Missing arguments for circle_property_chord_perpendicular_bisect_chord",

                    details="Expected format: circle_property_chord_perpendicular_bisect_chord(version, <circle>, <bisector_line>, <chord>)"

                )

            circle_token = args[1].strip()  # e.g., "O"

            bisector_line = args[2].strip()  # e.g., "PM"

            chord_token = args[3].strip()  # e.g., "AB"

            # Record the fact for later use

            if not hasattr(self, "bisector_facts"):
                self.bisector_facts = set()

            self.bisector_facts.add((bisector_line, chord_token))

            print(f"Recorded fact: {bisector_line} is the perpendicular bisector of {chord_token}")

            # Find the midpoint from collinear facts

            midpoint = None

            for fact in self.collinear_facts:

                if set(chord_token).issubset(set(fact)):

                    extras = [pt for pt in fact if pt not in chord_token]

                    if extras:
                        midpoint = extras[0]

                        break

            if midpoint is not None:

                print(f"Found midpoint for chord {chord_token}: {midpoint}")

                # Verify the midpoint is on the bisector line

                if midpoint in bisector_line:

                    # Find the other endpoint of the bisector line

                    other_endpoint = next((pt for pt in bisector_line if pt != midpoint), None)

                    if other_endpoint is not None:

                        # For both versions, add constraints for both perpendicular and equal segments

                        # 1. Add perpendicular constraint (90° angle)

                        angle1 = self.add_angle(chord_token[0], midpoint, other_endpoint)

                        angle2 = self.add_angle(other_endpoint, midpoint, chord_token[1])

                        self.solver.add(angle1 == 90, angle2 == 90)

                        print(
                            f"Added perpendicular constraints: angle({chord_token[0]}{midpoint}{other_endpoint}) and angle({other_endpoint}{midpoint}{chord_token[1]}) = 90°")

                        # 2. Add bisection constraint (equal segments)

                        len_first = self.add_length(chord_token[0], midpoint)

                        len_second = self.add_length(midpoint, chord_token[1])

                        self.solver.add(len_first == len_second)

                        print(
                            f"Added chord bisection constraint: {chord_token[0]}{midpoint} = {midpoint}{chord_token[1]}")

                        # 3. Record the perpendicular bisector relationship

                        if not hasattr(self, "perpendicular_bisectors"):
                            self.perpendicular_bisectors = set()

                        self.perpendicular_bisectors.add((bisector_line, chord_token))

                        print(f"Recorded perpendicular bisector relationship: {bisector_line} ⊥ {chord_token}")

                        # Add conclusion to tangent_facts as mentioned in original code

                        self.tangent_facts.add(("IsPerpendicularBisectorOfLine", (bisector_line, chord_token)))

                    else:

                        print(f"Could not determine the other endpoint of bisector {bisector_line}.")

                else:

                    print(f"Midpoint {midpoint} is not on bisector line {bisector_line}; cannot add constraints.")

            else:

                print(f"No midpoint identified for chord {chord_token}; cannot add constraints.")

            return None






        elif theorem_name == "radius_of_circle_property_length_equal":
            # Expecting arguments: [version, line_token, circle_token] e.g., ("1", "OA", "O")
            if len(args) < 3:
                return GeometricError(
                    tier=ErrorTier.TIER1_THEOREM_CALL_SYNTAX_VIOLATION,
                    message="Missing arguments for radius_of_circle_property_length_equal",
                    details="Expected format: radius_of_circle_property_length_equal(1, <line>, <circle>)"
                )
            line_token = args[1].strip()  # e.g., "OA"
            circle_token = args[2].strip()  # e.g., "O"
            # Ensure that a radius variable exists for the circle.
            if circle_token not in self.circle_radii:
                radius_var = Real(f"radius_{circle_token}")
                self.circle_radii[circle_token] = radius_var
                self.solver.add(radius_var >= 0)
            else:
                radius_var = self.circle_radii[circle_token]
            # Get (or create) the length variable for the given line.
            length_var = self.add_length(line_token[0], line_token[1])
            # Add the constraint that the line’s length equals the circle’s radius.
            self.solver.add(length_var == radius_var)
            print(f"Added radius property: LengthOfLine({line_token}) = RadiusOfCircle({circle_token})")


        elif theorem_name == "parallel_property_ipsilateral_internal_angle":
            # Expected conclusion: Equal(Add(MeasureOfAngle(BAD),MeasureOfAngle(ADC)),180)
            # We use a regex to capture the two angle tokens.
            pattern = r'Equal\(Add\(MeasureOfAngle\((\w{3})\),MeasureOfAngle\((\w{3})\)\),180\)'
            m = re.match(pattern, conclusions[0])
            if m:
                angle1_token, angle2_token = m.groups()  # e.g. "BAD" and "ADC"
                # Create the corresponding Z3 variables for these angles using your helper.
                angle1_var = self.add_angle(angle1_token[0], angle1_token[1], angle1_token[2])
                angle2_var = self.add_angle(angle2_token[0], angle2_token[1], angle2_token[2])
                # Add the constraint that their sum equals 180.
                self.solver.add(angle1_var + angle2_var == 180)
                print(f"Added ipsilateral internal angle constraint: {angle1_token} + {angle2_token} = 180")
            else:
                return GeometricError(
                    tier=ErrorTier.TIER1_THEOREM_CALL_SYNTAX_VIOLATION,
                    message="Conclusion format error for parallel_property_ipsilateral_internal_angle",
                    details=f"Expected pattern not found in: {conclusions[0]}"
                )


        elif theorem_name == "tangent_of_circle_property_perpendicular":

            version = args[0]

            if version == "1":

                tangent_line = args[1]  # e.g., "AM"

                center = args[2]  # e.g., "O"

                # For version 1, assume tangent_line is [external point][tangency point]

                tangency_point = tangent_line[1]

                tangent_other = tangent_line[0]

                angle_name = tangent_other + tangency_point + center  # e.g., "AMO"

                normalized_angle = self.normalize_angle_name(angle_name)

                angle_var = self.add_angle(normalized_angle[0], normalized_angle[1], normalized_angle[2])

                self.solver.add(angle_var == 90)

                print(
                    f"[Version 1] Added tangent perpendicular constraint: {tangent_line} ⟂ {center}{tangency_point} (angle {normalized_angle} = 90)")

            elif version == "2":

                tangent_line = args[1]  # e.g., "AN"

                center = args[2]  # e.g., "O"

                tangency_point = tangent_line[1]

                tangent_other = tangent_line[0]

                # For version 2, we might define the angle in a different order:

                angle_name = center + tangency_point + tangent_other  # e.g., "ONA"

                normalized_angle = self.normalize_angle_name(angle_name)

                angle_var = self.add_angle(normalized_angle[0], normalized_angle[1], normalized_angle[2])

                self.solver.add(angle_var == 90)

                print(
                    f"[Version 2] Added tangent perpendicular constraint: {tangent_line} ⟂ {center}{tangency_point} (angle {normalized_angle} = 90)")

            else:

                return GeometricError(

                    tier=ErrorTier.TIER1_THEOREM_CALL_SYNTAX_VIOLATION,

                    message=f"Unsupported version {version} for tangent_of_circle_property_perpendicular"

                )






        elif theorem_name == "arc_property_center_angle":

            version = args[0]

            if version == "1":

                arc_name = args[1]  # e.g., "OMN"

                center = args[2]  # e.g., "O"

                arc_var = self.add_arc(arc_name)

                # Expected conclusion: "Equal(MeasureOfArc(OMN),MeasureOfAngle(NOM))"

                pattern = r'Equal\(MeasureOfArc\(' + re.escape(arc_name) + r'\),MeasureOfAngle\((\w{3})\)\)'

                m = re.search(pattern, conclusions[0])

                if m:

                    angle_str = m.group(1)  # e.g., "NOM"

                    angle_var = self.add_angle(angle_str[0], angle_str[1], angle_str[2])

                    self.solver.add(arc_var == angle_var)

                    print(f"Added arc center angle constraint: MeasureOfArc({arc_name}) == MeasureOfAngle({angle_str})")

                else:

                    return GeometricError(

                        tier=ErrorTier.TIER1_THEOREM_CALL_SYNTAX_VIOLATION,

                        message="Conclusion format error for arc_property_center_angle",

                        details=f"Error 1. not the expected pattern of the conclution for this theorem"

                    )

            else:

                return GeometricError(

                    tier=ErrorTier.TIER1_THEOREM_CALL_SYNTAX_VIOLATION,

                    message=f"Version {version} for arc_property_center_angle not implemented"

                )









        elif theorem_name == "arc_property_circumference_angle_external":

            version = args[0]

            if version == "1":

                arc_name = args[1]  # e.g., "OMN"

                external_point = args[2]  # e.g., "B"

                arc_var = self.add_arc(arc_name)

                # Expected conclusion: "Equal(MeasureOfAngle(NBM),Mul(MeasureOfArc(OMN),1/2))"

                pattern = r'Equal\(MeasureOfAngle\((\w{3})\),Mul\(MeasureOfArc\(' + re.escape(arc_name) + r'\),1/2\)\)'

                m = re.search(pattern, conclusions[0])

                if m:

                    angle_str = m.group(1)  # e.g., "NBM"

                    angle_var = self.add_angle(angle_str[0], angle_str[1], angle_str[2])

                    from fractions import Fraction

                    self.solver.add(angle_var == arc_var * Fraction(1, 2))

                    print(
                        f"Added arc circumference external angle constraint: MeasureOfAngle({angle_str}) == 1/2 * MeasureOfArc({arc_name})")

                else:

                    return GeometricError(

                        tier=ErrorTier.TIER1_THEOREM_CALL_SYNTAX_VIOLATION,

                        message="Conclusion format error for arc_property_circumference_angle_external",

                        details=f"Expected pattern Equal(MeasureOfAngle(XXX),Mul(MeasureOfArc({arc_name}),1/2)) but got {conclusions[0]}"

                    )

            else:

                return GeometricError(

                    tier=ErrorTier.TIER1_THEOREM_CALL_SYNTAX_VIOLATION,

                    message=f"Version {version} for arc_property_circumference_angle_external not implemented"

                )





        elif theorem_name == "diameter_of_circle_property_right_angle":
            # conclusion is typically: ["PerpendicularBetweenLine(BC,AC)"]
            # So parse that: "PerpendicularBetweenLine(BC,AC)" => means angle BCA = 90
            conc = conclusions[0]
            m = re.match(r'PerpendicularBetweenLine\((\w+),(\w+)\)', conc)
            if m:
                line1, line2 = m.groups()
                # to impose perpendicular we do an angle of 90
                # e.g. if line1=BC, line2=AC, the shared point is C => angle BCA=90
                # Find the common letter. Usually the middle letter is the vertex
                vertex = None
                for p in line1:
                    if p in line2:
                        vertex = p
                        break
                if vertex is None or len(vertex) == 0:
                    # could raise an error, but let's just skip
                    return None
                # the other points are the endpoints
                # e.g. line1=BC => B or C is vertex, line2=AC => A or C is vertex
                # so angle is BCA or CBA or etc. We want the one that puts 'C' in the middle
                # we can do a quick check:
                other1 = [p for p in line1 if p != vertex][0]
                other2 = [p for p in line2 if p != vertex][0]
                angle_name = other1 + vertex + other2
                angle_name = self.normalize_angle_name(angle_name)
                angle_var = self.add_angle(angle_name[0], angle_name[1], angle_name[2])
                self.solver.add(angle_var == 90)
                print(f"diameter_of_circle_property_right_angle => set angle {angle_name} = 90")



        elif theorem_name == "mirror_similar_triangle_judgment_aa":
            match = re.search(r'MirrorSimilarBetweenTriangle\((\w+),(\w+)\)', conclusions[0])
            if match:
                tri1, tri2 = match.groups()
                print(f"Adding mirror similarity: {tri1} and {tri2} are mirror similar by AA.")
                self.add_mirror_similar_triangles(tri1, tri2)
            else:
                return GeometricError(
                    tier=ErrorTier.TIER1_THEOREM_CALL_SYNTAX_VIOLATION,
                    message="Conclusion format error for mirror_similar_triangle_judgment_aa",
                    details=f"Expected format: MirrorSimilarBetweenTriangle(XXX,YYY) but got {conclusions[0]}"
                )





        elif theorem_name == "cosine_theorem":

            version = args[0]

            if version == "1":

                # Parse the conclusion pattern

                # The law of cosines pattern based on your example:

                # AC² + 2*BA*BC*cos(CBA) = BA² + BC²

                pattern = r'Equal\(Add\(Pow\(LengthOfLine\((\w+)\),2\),Mul\(2,LengthOfLine\((\w+)\),LengthOfLine\((\w+)\),Cos\(MeasureOfAngle\((\w+)\)\)\)\),Add\(Pow\(LengthOfLine\((\w+)\),2\),Pow\(LengthOfLine\((\w+)\),2\)\)\)'

                match = re.search(pattern, conclusions[0])

                if match:

                    side1, side2, side3, angle_str, side4, side5 = match.groups()

                    # Verify sides match the expected pattern

                    if side2 != side4 or side3 != side5:
                        return GeometricError(

                            tier=ErrorTier.TIER1_THEOREM_CALL_SYNTAX_VIOLATION,

                            message="Conclusion format error for cosine_theorem",

                            details=f"Sides in conclusion don't match expected pattern: {side2} != {side4} or {side3} != {side5}"

                        )

                    # Get or create variables for sides and angle

                    length1_var = self.add_length(side1[0], side1[1])

                    length2_var = self.add_length(side2[0], side2[1])

                    length3_var = self.add_length(side3[0], side3[1])

                    angle_var = self.add_angle(angle_str[0], angle_str[1], angle_str[2])

                    # Create or get cosine variable for the angle

                    cos_var_name = f"cos_{angle_str}"

                    if cos_var_name not in self.variables:
                        self.variables[cos_var_name] = Real(cos_var_name)

                        self.solver.add(self.variables[cos_var_name] >= -1)

                        self.solver.add(self.variables[cos_var_name] <= 1)

                    cos_var = self.variables[cos_var_name]

                    # Check if the solver is satisfiable

                    if self.solver.check() == sat:

                        model = self.solver.model()

                        # Check if angle has a unique value

                        angle_unique = False

                        angle_val = None

                        cos_val = None

                        try:

                            # Get the current angle value from the model

                            a_val_str = model.eval(angle_var).as_decimal(10)

                            if a_val_str.endswith('?'):
                                a_val_str = a_val_str[:-1]

                            angle_val = float(a_val_str)

                            # Check if this value is uniquely determined

                            temp_solver = Solver()

                            for c in self.solver.assertions():
                                temp_solver.add(c)

                            epsilon = 1e-6

                            temp_solver.add(Or(

                                angle_var < angle_val - epsilon,

                                angle_var > angle_val + epsilon

                            ))

                            if temp_solver.check() == unsat:
                                # Angle is uniquely determined

                                angle_unique = True

                                import math

                                cos_val = math.cos(math.radians(angle_val))

                                print(f"Angle {angle_str} has unique value {angle_val}°, cos = {cos_val}")

                                # Add the cosine value to the variable

                                self.solver.add(cos_var == cos_val)

                        except Exception as e:

                            print(f"Error checking angle: {e}")

                        # Add the law of cosines constraint in the exact format from the conclusion

                        # AC² + 2*BA*BC*cos(CBA) = BA² + BC²

                        self.solver.add(

                            length1_var ** 2 + 2 * length2_var * length3_var * cos_var == length2_var ** 2 + length3_var ** 2)

                        print(f"Added cosine theorem constraint for triangle with angle {angle_str}")



                    else:

                        # IMPROVED ERROR HANDLING

                        # Get the contradictory constraints to provide better feedback

                        contradictory_constraints = self.find_contradictory_constraints()

                        details = "No specific contradictory constraints found."

                        if contradictory_constraints:

                            details = "Contradictory constraints:\n"

                            for constraint in contradictory_constraints:
                                details += f"  {constraint}\n"

                        # Include angle constraints

                        angle_constraints = []

                        for c in self.solver.assertions():

                            c_str = str(c)

                            if f"angle_{angle_str}" in c_str or f"cos_" in c_str:
                                angle_constraints.append(self.format_constraint(c_str))

                        if angle_constraints:

                            details += "\nRelevant angle constraints:\n"

                            for constraint in angle_constraints:
                                details += f"  {constraint}\n"

                        # Include length constraints

                        length_constraints = []

                        for c in self.solver.assertions():

                            c_str = str(c)

                            if (f"length_{side1}" in c_str or

                                    f"length_{side2}" in c_str or

                                    f"length_{side3}" in c_str):
                                length_constraints.append(self.format_constraint(c_str))

                        if length_constraints:

                            details += "\nRelevant length constraints:\n"

                            for constraint in length_constraints:
                                details += f"  {constraint}\n"

                        # Include right triangle constraints if applicable

                        if self.right_triangles:

                            details += "\nRight triangles defined in the system:\n"

                            for tri in self.right_triangles:
                                details += f"  {tri}\n"

                        return GeometricError(

                            tier=ErrorTier.TIER2_PREMISE_VIOLATION,

                            message="Solver unsat when trying to evaluate angles for cosine theorem",

                            details=details

                        )

                else:

                    return GeometricError(

                        tier=ErrorTier.TIER1_THEOREM_CALL_SYNTAX_VIOLATION,

                        message="Conclusion format error for cosine_theorem",

                        details=f"Expected pattern not found in: {conclusions[0]}"

                    )

            else:

                return GeometricError(

                    tier=ErrorTier.TIER1_THEOREM_CALL_SYNTAX_VIOLATION,

                    message=f"Unsupported version {version} for cosine_theorem"

                )




        elif theorem_name == "sine_theorem":

            version = args[0]

            if version == "1":

                # Parse the conclusion pattern

                pattern = r'Equal\(Mul\(LengthOfLine\((\w{2})\),Sin\(MeasureOfAngle\((\w{3})\)\)\),Mul\(LengthOfLine\((\w{2})\),Sin\(MeasureOfAngle\((\w{3})\)\)\)\)'

                match = re.search(pattern, conclusions[0])

                import math

                if match:

                    side1, angle1_str, side2, angle2_str = match.groups()

                    # Get or create variables for sides and angles

                    length1_var = self.add_length(side1[0], side1[1])

                    length2_var = self.add_length(side2[0], side2[1])

                    angle1_var = self.add_angle(angle1_str[0], angle1_str[1], angle1_str[2])

                    angle2_var = self.add_angle(angle2_str[0], angle2_str[1], angle2_str[2])

                    # Create or get sine variables for both angles
                    start_first, vertex_first, end_first = angle1_str[0], angle1_str[1], angle1_str[2]
                    start_second, vertex_second, end_second = angle2_str[0], angle2_str[1], angle2_str[2]
                    if start_first > end_first:
                        # Swap start and end if needed to maintain alphabetical order
                        angle1_str = end_first + vertex_first + start_first
                    if start_second > end_second:
                        # Swap start and end if needed to maintain alphabetical order
                        angle2_str = end_second + vertex_second + start_second
                    sin1_var_name = f"sin_{angle1_str}"

                    sin2_var_name = f"sin_{angle2_str}"

                    if sin1_var_name not in self.variables:
                        self.variables[sin1_var_name] = Real(sin1_var_name)

                        self.solver.add(self.variables[sin1_var_name] >= 0)

                        self.solver.add(self.variables[sin1_var_name] <= 1)

                    if sin2_var_name not in self.variables:
                        self.variables[sin2_var_name] = Real(sin2_var_name)

                        self.solver.add(self.variables[sin2_var_name] >= 0)

                        self.solver.add(self.variables[sin2_var_name] <= 1)

                    sin1_var = self.variables[sin1_var_name]

                    sin2_var = self.variables[sin2_var_name]

                    # Check if the solver is satisfiable

                    if self.solver.check() == sat:

                        model = self.solver.model()

                        # Initialize flags for unique angle values

                        angle1_unique = False

                        angle2_unique = False

                        angle1_val = None

                        angle2_val = None

                        sin1_val = None

                        sin2_val = None

                        # Check angle1 (e.g., BAC)

                        try:

                            # Get the current angle value from the model

                            a1_val_str = model.eval(angle1_var).as_decimal(10)

                            if a1_val_str.endswith('?'):
                                a1_val_str = a1_val_str[:-1]

                            angle1_val = float(a1_val_str)

                            # Check if this value is uniquely determined

                            temp_solver = Solver()

                            for c in self.solver.assertions():
                                temp_solver.add(c)

                            epsilon = 1e-6

                            temp_solver.add(Or(

                                angle1_var < angle1_val - epsilon,

                                angle1_var > angle1_val + epsilon

                            ))

                            if temp_solver.check() == unsat:
                                # Angle is uniquely determined

                                angle1_unique = True

                                sin1_val = math.sin(math.radians(angle1_val))

                                print(f"Angle {angle1_str} has unique value {angle1_val}°, sin = {sin1_val}")

                                # Add the sine value to the variable

                                self.solver.add(sin1_var == sin1_val)

                        except Exception as e:

                            print(f"Error checking angle1: {e}")

                        # Check angle2 (e.g., ACB)

                        try:

                            # Get the current angle value from the model

                            a2_val_str = model.eval(angle2_var).as_decimal(10)

                            if a2_val_str.endswith('?'):
                                a2_val_str = a2_val_str[:-1]

                            angle2_val = float(a2_val_str)

                            # Check if this value is uniquely determined

                            temp_solver = Solver()

                            for c in self.solver.assertions():
                                temp_solver.add(c)

                            epsilon = 1e-6

                            temp_solver.add(Or(

                                angle2_var < angle2_val - epsilon,

                                angle2_var > angle2_val + epsilon

                            ))

                            if temp_solver.check() == unsat:

                                # Angle is uniquely determined

                                angle2_unique = True

                                sin2_val = math.sin(math.radians(angle2_val))

                                print(f"Angle {angle2_str} has unique value {angle2_val}°, sin = {sin2_val}")

                                # Add the sine value to the variable

                                self.solver.add(sin2_var == sin2_val)

                                # Check specifically for 90 degree angles

                                if abs(angle2_val - 90.0) < epsilon:
                                    print(f"Angle {angle2_str} is 90 degrees, setting sin({angle2_str}) = 1.0")

                                    self.solver.add(sin2_var == 1.0)

                        except Exception as e:

                            print(f"Error checking angle2: {e}")

                        # Now add the Law of Sines constraint with the right pairing

                        if angle1_unique and angle2_unique:

                            # Both angles have unique values, use those directly

                            self.solver.add(length1_var * sin1_val == length2_var * sin2_val)

                            print(
                                f"Added sine theorem constraint with known values: {side1} * {sin1_val} = {side2} * {sin2_val}")

                        elif angle1_unique:

                            # Only angle1 is unique

                            self.solver.add(length1_var * sin1_val == length2_var * sin2_var)

                            print(
                                f"Added sine theorem constraint with partial known values: {side1} * {sin1_val} = {side2} * sin({angle2_str})")

                        elif angle2_unique:

                            # Only angle2 is unique

                            self.solver.add(length1_var * sin1_var == length2_var * sin2_val)

                            print(
                                f"Added sine theorem constraint with partial known values: {side1} * sin({angle1_str}) = {side2} * {sin2_val}")

                        else:

                            # Neither angle has a unique value, but match the sides with their corresponding angles

                            self.solver.add(length1_var * sin1_var == length2_var * sin2_var)

                            print(
                                f"Added sine theorem constraint with variables: {side1} * sin({angle1_str}) = {side2} * sin({angle2_str})")

                        # Additional check specifically for right triangles

                        # This ensures any 90-degree angle is explicitly handled

                        for angle_str, angle_var, sin_var in [(angle1_str, angle1_var, sin1_var),
                                                              (angle2_str, angle2_var, sin2_var)]:

                            # Check if this angle is constrained to be 90 degrees

                            right_angle_solver = Solver()

                            for c in self.solver.assertions():
                                right_angle_solver.add(c)

                            right_angle_solver.add(angle_var != 90)

                            if right_angle_solver.check() == unsat:
                                # This is a 90-degree angle, set sin = 1

                                self.solver.add(sin_var == 1.0)

                                print(f"Added constraint for right angle: sin({angle_str}) = 1.0")

                        return None

                    else:

                        # IMPROVED ERROR HANDLING

                        # Get the contradictory constraints to provide better feedback

                        contradictory_constraints = self.find_contradictory_constraints()

                        details = "No specific contradictory constraints found."

                        if contradictory_constraints:

                            details = "Contradictory constraints:\n"

                            for constraint in contradictory_constraints:
                                details += f"  {constraint}\n"

                        # Also include any angle constraints

                        angle_constraints = []

                        for c in self.solver.assertions():

                            c_str = str(c)

                            if f"angle_{angle1_str}" in c_str or f"angle_{angle2_str}" in c_str or f"sin_" in c_str:
                                angle_constraints.append(self.format_constraint(c_str))

                        if angle_constraints:

                            details += "\nRelevant angle constraints:\n"

                            for constraint in angle_constraints:
                                details += f"  {constraint}\n"

                        # Add length constraints

                        length_constraints = []

                        for c in self.solver.assertions():

                            c_str = str(c)

                            if f"length_{side1}" in c_str or f"length_{side2}" in c_str:
                                length_constraints.append(self.format_constraint(c_str))

                        if length_constraints:

                            details += "\nRelevant length constraints:\n"

                            for constraint in length_constraints:
                                details += f"  {constraint}\n"

                        return GeometricError(

                            tier=ErrorTier.TIER2_PREMISE_VIOLATION,

                            message="Solver unsat when trying to evaluate angles for sine theorem",

                            details=details

                        )

                else:

                    return GeometricError(

                        tier=ErrorTier.TIER1_THEOREM_CALL_SYNTAX_VIOLATION,

                        message="Conclusion format error for sine_theorem",

                        details=f"Expected pattern Equal(Mul(LengthOfLine(XX),Sin(MeasureOfAngle(XXX))),Mul(LengthOfLine(XX),Sin(MeasureOfAngle(XXX)))) but got {conclusions[0]}"

                    )

            elif version == "2":

                print("Version 2 of sine_theorem not implemented")

                return None






        elif theorem_name == "mirror_similar_triangle_property_line_ratio":
            match = re.search(
                r'Equal\(LengthOfLine\((\w+)\),Mul\(LengthOfLine\((\w+)\),RatioOfMirrorSimilarTriangle\((\w+),(\w+)\)\)\)',
                conclusions[0]
            )
            if match:
                line1, line2, tri1, tri2 = match.groups()
                norm_tris = self.canonicalize_mirror_triangle_pair(tri1, tri2)
                if not norm_tris:
                    return GeometricError(
                        tier=ErrorTier.TIER1_THEOREM_CALL_SYNTAX_VIOLATION,
                        message=f"Invalid triangle names in mirror_similar_triangle_property_line_ratio: {tri1}, {tri2}"
                    )
                if norm_tris not in self.mirror_triangle_ratios:
                    var_name = f"ratio_mirror_{norm_tris[0]}_{norm_tris[1]}"
                    self.mirror_triangle_ratios[norm_tris] = Real(var_name)
                ratio = self.mirror_triangle_ratios[norm_tris]
                line1_var = self.add_length(line1[0], line1[1])
                line2_var = self.add_length(line2[0], line2[1])
                self.solver.add(line1_var == line2_var * ratio)
                print(
                    f"Added mirror similar triangle ratio constraint: LengthOfLine({line1}) = LengthOfLine({line2}) * RatioOfMirrorSimilarTriangle({tri1},{tri2})")
            else:
                return GeometricError(
                    tier=ErrorTier.TIER1_THEOREM_CALL_SYNTAX_VIOLATION,
                    message="Conclusion format error for mirror_similar_triangle_property_line_ratio",
                    details=f"Expected format: Equal(LengthOfLine(XXX),Mul(LengthOfLine(YYY),RatioOfMirrorSimilarTriangle(ZZZ,WWW))) but got {conclusions[0]}"
                )





        elif theorem_name == "triangle_area_formula_sine":

            # Expected conclusion format (for example):

            # "Equal(AreaOfTriangle(CAB),Mul(LengthOfLine(CA),LengthOfLine(CB),Sin(MeasureOfAngle(BCA)),1/2))"

            c = conclusions[0]

            pat = r"Equal\(AreaOfTriangle\((\w+)\),Mul\(LengthOfLine\((\w+)\),LengthOfLine\((\w+)\),Sin\(MeasureOfAngle\((\w{3})\)\),([\d/\.]+)\)\)"

            mm = re.match(pat, c)

            if mm:

                tri_name, side1, side2, angle_name, factor_str = mm.groups()

                # Ensure an area variable exists for the triangle.
                normalized_tri_name = ''.join(sorted(tri_name))
                # Then use normalized_tri_name instead of tri_name
                if normalized_tri_name not in self.triangle_areas:
                    self.triangle_areas[normalized_tri_name] = Real(f"areaTriangle_{normalized_tri_name}")
                    self.solver.add(self.triangle_areas[normalized_tri_name] >= 0)

                area_var = self.triangle_areas[normalized_tri_name]

                # Get the side length variables.

                side1_var = self.add_length(side1[0], side1[1])

                side2_var = self.add_length(side2[0], side2[1])

                # Get the angle variable.

                angle_var = self.add_angle(angle_name[0], angle_name[1], angle_name[2])

                # Convert the factor (e.g. "1/2") to a float.

                try:

                    factor_value = float(eval(factor_str))

                except Exception as e:

                    print(f"Error evaluating factor {factor_str}: {e}. Defaulting to 0.5.")

                    factor_value = 0.5

                # Try to evaluate the angle numerically so we can compute its sine.

                if self.solver.check() == sat:

                    model = self.solver.model()

                    # Use model_completion=True in case the angle variable has a default value.

                    a_val_str = model.eval(angle_var, model_completion=True).as_decimal(10)

                    if a_val_str.endswith('?'):
                        a_val_str = a_val_str[:-1]

                    try:

                        from fractions import Fraction

                        angle_val = float(Fraction(a_val_str))

                    except Exception as e:

                        return GeometricError(

                            tier=ErrorTier.TIER2_PREMISE_VIOLATION,

                            message="Cannot convert angle value to float in triangle_area_formula_sine step",

                            details=str(e)

                        )

                    import math

                    # Compute the sine (note: math.sin expects radians).

                    sin_val = round(math.sin(math.radians(angle_val)), 10)

                    # Now add the constraint with the computed sine value.

                    self.solver.add(area_var == factor_value * side1_var * side2_var * sin_val)

                    print(
                        f"[triangle_area_formula_sine] Added constraint: AreaOfTriangle({tri_name}) = {factor_value} * LengthOfLine({side1}) * LengthOfLine({side2}) * {sin_val}")

                else:

                    return GeometricError(

                        tier=ErrorTier.TIER2_PREMISE_VIOLATION,

                        message="Solver unsat when evaluating angle for triangle_area_formula_sine",

                    )

            else:

                return GeometricError(

                    tier=ErrorTier.TIER1_THEOREM_CALL_SYNTAX_VIOLATION,

                    message="Conclusion format error for triangle_area_formula_sine",

                    details=f"Expected pattern Equal(AreaOfTriangle(XXX),Mul(LengthOfLine(YY),LengthOfLine(ZZ),Sin(MeasureOfAngle(AAA)),factor)) but got {conclusions[0]}"

                )




        elif theorem_name == "right_triangle_judgment_angle":
            # Expecting a theorem call like: right_triangle_judgment_angle(1,GHE)
            # and a conclusion list like: ["RightTriangle(GHE)"]
            version = args[0]
            if version == "1":
                if len(args) < 2:
                    return GeometricError(
                        tier=ErrorTier.TIER1_THEOREM_CALL_SYNTAX_VIOLATION,
                        message="Missing triangle argument for right_triangle_judgment_angle",
                        details="Expected right_triangle_judgment_angle(1, triangle)"
                    )
                triangle = args[1].strip()
                # Call the helper to mark this triangle as a right triangle.
                # This method adds the constraint that the angle (using the first point as vertex)
                # is equal to 90.
                self.add_right_triangle(triangle)
                print(f"Added right triangle judgment: {triangle} is a right triangle (angle = 90).")
            elif version == "2":
                print("2")





        elif theorem_name == "triangle_area_formula_sine":
            # conclusion: "Equal(AreaOfTriangle(CAB),Mul(LengthOfLine(CA),LengthOfLine(CB),Sin(MeasureOfAngle(ACB)),1/2))"
            c = conclusions[0]
            pattern = r"Equal\(AreaOfTriangle\((\w+)\),Mul\(LengthOfLine\((\w+)\),LengthOfLine\((\w+)\),Sin\(MeasureOfAngle\((\w+)\)\),(.*?)\)\)"
            mm = re.match(pattern, c)
            if mm:
                tri, side1, side2, angle_str, factor_str = mm.groups()
                # We'll just store the relationship for a later numeric pass:
                self.proven_area_relationships.append(
                    ("triangle_area_sine", tri, side1, side2, angle_str, factor_str)
                )
                print(
                    f"[triangle_area_formula_sine] Stored relationship for {tri} = ½·{side1}·{side2}·sin({angle_str})")


        elif theorem_name == "diameter_of_circle_property_length_equal":
            # conclusion e.g.: "Equal(LengthOfLine(BA),DiameterOfCircle(D))"
            conc = conclusions[0]
            m = re.match(r'Equal\(LengthOfLine\((\w+)\),DiameterOfCircle\((\w+)\)\)', conc)
            if m:
                line_name, circle_name = m.groups()
                # create a Real for diameterOfCircle(D) if not exist
                diam_name = f"diameter_{circle_name}"
                if diam_name not in self.circle_diameters:
                    self.circle_diameters[diam_name] = Real(diam_name)
                    self.solver.add(self.circle_diameters[diam_name] >= 0)
                # get the line length
                ln_var = self.add_length(line_name[0], line_name[1])
                # set them equal
                self.solver.add(ln_var == self.circle_diameters[diam_name])
                print(f"diameter_of_circle_property_length_equal => {line_name} = diameter_{circle_name}")


        elif theorem_name == "circle_property_length_of_radius_and_diameter":
            # "Equal(DiameterOfCircle(D),Mul(RadiusOfCircle(D),2))"
            c = conclusions[0]
            mm = re.match(r'Equal\(DiameterOfCircle\((\w+)\),Mul\(RadiusOfCircle\((\w+)\),([\d/\.]+)\)\)', c)
            if mm:
                circle_diam, circle_rad, factor_str = mm.groups()
                # e.g. circle_diam=="D", circle_rad=="D", factor_str=="2"
                diam_name = f"diameter_{circle_diam}"
                rad_name = f"radius_{circle_rad}"
                if diam_name not in self.circle_diameters:
                    self.circle_diameters[diam_name] = Real(diam_name)
                    self.solver.add(self.circle_diameters[diam_name] >= 0)
                if circle_rad not in self.circle_radii:
                    self.circle_radii[circle_rad] = Real(rad_name)
                    self.solver.add(self.circle_radii[circle_rad] >= 0)
                factor_val = float(eval(factor_str))  # typically 2
                self.solver.add(self.circle_diameters[diam_name] == self.circle_radii[circle_rad] * factor_val)
                print(
                    f"circle_property_length_of_radius_and_diameter => diameter_{circle_diam} = 2 * radius_{circle_rad}")



        elif theorem_name == "circle_area_formula":

            # Expecting: "Equal(AreaOfCircle(D),Mul(pi,RadiusOfCircle(D),RadiusOfCircle(D)))"

            c = conclusions[0]

            mm = re.match(r'Equal\(AreaOfCircle\((\w+)\),Mul\(pi,RadiusOfCircle\((\w+)\),RadiusOfCircle\(\2\)\)\)', c)

            if mm:

                circle_area, circle_rad = mm.groups()

                if circle_area not in self.circle_areas:
                    self.circle_areas[circle_area] = Real(f"area_{circle_area}")

                    self.solver.add(self.circle_areas[circle_area] >= 0)

                if circle_rad not in self.circle_radii:
                    self.circle_radii[circle_rad] = Real(f"radius_{circle_rad}")

                    self.solver.add(self.circle_radii[circle_rad] >= 0)

                Avar = self.circle_areas[circle_area]

                Rvar = self.circle_radii[circle_rad]

                # Use the symbolic pi_sym instead of a numerical value.

                self.solver.add(Avar == self.pi * (Rvar * Rvar))

                print(f"circle_area_formula => area_{circle_area} = pi * radius_{circle_rad}^2")





        elif theorem_name == "parallel_property_corresponding_angle":

            version = args[0]

            if version == "1":

                # Expected conclusion (version 1), e.g.:

                # ["Equal(MeasureOfAngle(AEF),MeasureOfAngle(EDH))"]

                m = re.search(r'Equal\(MeasureOfAngle\((\w{3})\),\s*MeasureOfAngle\((\w{3})\)\)', conclusions[0])

                if m:

                    angle1, angle2 = m.group(1), m.group(2)

                    a1 = self.add_angle(angle1[0], angle1[1], angle1[2])

                    a2 = self.add_angle(angle2[0], angle2[1], angle2[2])

                    self.solver.add(a1 == a2)

                    print(f"[Version 1] Added parallel corresponding angle equality: {angle1} == {angle2}")

                else:

                    return GeometricError(

                        tier=ErrorTier.TIER1_THEOREM_CALL_SYNTAX_VIOLATION,

                        message="Conclusion format error for parallel_property_corresponding_angle (version 1)",

                        details="Expected format: Equal(MeasureOfAngle(XXX),MeasureOfAngle(YYY))"

                    )

            elif version == "2":

                # Expected conclusion (version 2), e.g.:

                # ["Equal(MeasureOfAngle(DHF),MeasureOfAngle(BFA))"]

                m = re.search(r'Equal\(MeasureOfAngle\((\w{3})\),\s*MeasureOfAngle\((\w{3})\)\)', conclusions[0])

                if m:

                    angle1, angle2 = m.group(1), m.group(2)

                    a1 = self.add_angle(angle1[0], angle1[1], angle1[2])

                    a2 = self.add_angle(angle2[0], angle2[1], angle2[2])

                    self.solver.add(a1 == a2)

                    print(f"[Version 2] Added parallel corresponding angle equality: {angle1} == {angle2}")

                else:

                    return GeometricError(

                        tier=ErrorTier.TIER1_THEOREM_CALL_SYNTAX_VIOLATION,

                        message="Conclusion format error for parallel_property_corresponding_angle (version 2)",

                        details="Expected format: Equal(MeasureOfAngle(XXX),MeasureOfAngle(YYY))"

                    )








        elif theorem_name == "triangle_property_angle_sum":

            # Expect a conclusion of the form:

            # "Equal(Add(MeasureOfAngle(CAB),MeasureOfAngle(ABC),MeasureOfAngle(BCA)),180)"
            version = args[0]
            if version == "1":
                match = re.search(

                    r'Equal\(Add\(MeasureOfAngle\((\w{3})\),MeasureOfAngle\((\w{3})\),MeasureOfAngle\((\w{3})\)\),180\)',

                    conclusions[0]

                )

                if match:

                    a1, a2, a3 = match.groups()  # e.g., "CAB", "ABC", "BCA"

                    # Add the three angle variables to the solver.

                    angle1_var = self.add_angle(a1[0], a1[1], a1[2])

                    angle2_var = self.add_angle(a2[0], a2[1], a2[2])

                    angle3_var = self.add_angle(a3[0], a3[1], a3[2])

                    # Impose the angle–sum constraint.

                    self.solver.add(angle1_var + angle2_var + angle3_var == 180)

                    print(f"Added triangle angle sum constraint: {a1} + {a2} + {a3} = 180")

                else:

                    return GeometricError(

                        tier=ErrorTier.TIER1_THEOREM_CALL_SYNTAX_VIOLATION,

                        message="Conclusion format error for triangle_property_angle_sum",

                        details=f"Expected pattern Equal(Add(MeasureOfAngle(XXX),MeasureOfAngle(YYY),MeasureOfAngle(ZZZ)),180) but got {conclusions[0]}"

                    )





        elif theorem_name == "similar_triangle_judgment_aa":
            # Expect a conclusion like ["SimilarBetweenTriangle(BAE,CAD)"]
            version = args[0]
            if version == "1":
                match = re.search(r'SimilarBetweenTriangle\((\w+),(\w+)\)', conclusions[0])
                if match:
                    tri1, tri2 = match.groups()
                    print(f"Adding that triangles {tri1} and {tri2} are similar by AA.")
                    self.add_similar_triangles(tri1, tri2)
                else:
                    return GeometricError(
                        tier=ErrorTier.TIER1_THEOREM_CALL_SYNTAX_VIOLATION,
                        message="Conclusion format error for similar_triangle_judgment_aa",
                        details=f"Expected SimilarBetweenTriangle(...) but got {conclusions[0]}"
                    )

            elif version == "2":
                print("2")




        elif theorem_name == "similar_triangle_property_line_ratio":

            version = args[0]

            if version == "1":

                # Parse conclusion like: Equal(LengthOfLine(CA),Mul(LengthOfLine(BC),RatioOfSimilarTriangle(DCA,DBC)))

                match = re.search(

                    r'Equal\(LengthOfLine\((\w+)\),'  # Group 1: line1 (e.g., CA)

                    r'Mul\(LengthOfLine\((\w+)\),'  # Group 2: line2 (e.g., BC)

                    r'RatioOfSimilarTriangle\((\w+),(\w+)\)\)\)',
                    # Group 3: tri1 (e.g., DCA), Group 4: tri2 (e.g., DBC)

                    conclusions[0]

                )

                if match:

                    line1, line2, tri1, tri2 = match.groups()

                    print(
                        f"Processing similar_triangle_property_line_ratio for {line1}, {line2} based on {tri1} ~ {tri2}")

                    # Normalize triangle pair for ratio lookup

                    norm_tris = self.normalize_similar_triangles(tri1, tri2)

                    if not norm_tris:
                        print(f"Error: Invalid triangle names '{tri1}', '{tri2}' for similarity.")

                        # Return error or handle gracefully

                        return GeometricError(

                            tier=ErrorTier.TIER1_THEOREM_CALL_SYNTAX_VIOLATION,

                            message=f"Invalid triangle names in similarity conclusion: {tri1}, {tri2}"

                        )

                    # Look up or create the ratio variable for this similarity pair

                    if norm_tris not in self.triangle_ratios:
                        var_name = f"ratio_{norm_tris[0]}_{norm_tris[1]}"

                        self.triangle_ratios[norm_tris] = Real(var_name)

                        # Add basic constraint: ratio > 0 (ratios are typically positive)

                        self.solver.add(self.triangle_ratios[norm_tris] > 0)

                        print(f"Created similarity ratio variable: {var_name}")

                    ratio = self.triangle_ratios[norm_tris]  # This is the Z3 Real variable for the ratio

                    # Add the fundamental symbolic constraint from the theorem's conclusion

                    try:

                        line1_var = self.add_length(line1[0], line1[1])

                        line2_var = self.add_length(line2[0], line2[1])

                    except IndexError:

                        print(f"Error: Invalid line name format '{line1}' or '{line2}'. Skipping constraint.")

                        return GeometricError(

                            tier=ErrorTier.TIER1_THEOREM_CALL_SYNTAX_VIOLATION,

                            message=f"Invalid line name format in similarity conclusion: {line1} or {line2}"

                        )

                    self.solver.add(line1_var == line2_var * ratio)

                    print(
                        f"Added symbolic similarity constraint: Length({line1}) == Length({line2}) * Ratio({tri1},{tri2})")

                    # --- Check for and apply known numeric ratio ---

                    norm_line1 = self.normalize_line_name(line1)

                    norm_line2 = self.normalize_line_name(line2)

                    known_ratio_val = None

                    if hasattr(self, 'numeric_length_ratios'):

                        # Check if ratio L1/L2 is known

                        if (norm_line1, norm_line2) in self.numeric_length_ratios:

                            known_ratio_val = self.numeric_length_ratios[(norm_line1, norm_line2)]

                            print(f"Found known numeric ratio {norm_line1}/{norm_line2} = {known_ratio_val}")

                        # Check if ratio L2/L1 is known

                        elif (norm_line2, norm_line1) in self.numeric_length_ratios:

                            known_ratio_inv = self.numeric_length_ratios[(norm_line2, norm_line1)]

                            if abs(known_ratio_inv) > 1e-9:  # Avoid division by zero

                                known_ratio_val = 1.0 / known_ratio_inv

                                print(
                                    f"Found known numeric ratio {norm_line2}/{norm_line1} = {known_ratio_inv}, derived {norm_line1}/{norm_line2} = {known_ratio_val}")

                    # If a numeric ratio was found, add an explicit constraint for the symbolic ratio variable

                    if known_ratio_val is not None:

                        # Optional: Check if ratio is already constrained to avoid redundancy

                        temp_solver = Solver()

                        for c in self.solver.assertions(): temp_solver.add(c)

                        epsilon = 1e-9  # Tolerance for float comparison

                        temp_solver.add(Or(ratio < known_ratio_val - epsilon, ratio > known_ratio_val + epsilon))

                        is_already_constrained = (temp_solver.check() == unsat)

                        if is_already_constrained:

                            print(
                                f"Ratio variable Ratio({tri1},{tri2}) already uniquely constrained to {known_ratio_val}. No new constraint needed.")

                        else:

                            self.solver.add(ratio == known_ratio_val)

                            print(
                                f"Added *explicit* Z3 constraint based on known numeric ratio: Ratio({tri1},{tri2}) == {known_ratio_val}")

                            # After explicitly setting the ratio, re-check satisfiability

                            if self.solver.check() == unsat:
                                print("ERROR: Adding explicit ratio constraint made the solver UNSATISFIABLE.")

                                # Optionally return an error here

                                # return GeometricError(...)

                    else:

                        print(
                            f"No known numeric ratio found for {norm_line1}/{norm_line2} to explicitly set Ratio({tri1},{tri2}). Relying on symbolic constraint.")

                    # --- End explicit ratio logic ---

                    # Call the function to add constraints for ALL corresponding sides

                    # This ensures consistency even if the conclusion only mentioned one pair

                    self.add_all_side_ratios_for_similar_triangles(tri1, tri2)

                    return None  # Indicate successful processing of this theorem step

                else:

                    # Handle case where the conclusion string doesn't match the expected pattern

                    print(
                        f"Error: Conclusion format incorrect for similar_triangle_property_line_ratio: {conclusions[0]}")

                    return GeometricError(

                        tier=ErrorTier.TIER1_THEOREM_CALL_SYNTAX_VIOLATION,

                        message="Conclusion format error for similar_triangle_property_line_ratio",

                        details=f"Expected format: Equal(LengthOfLine(L1),Mul(LengthOfLine(L2),RatioOfSimilarTriangle(T1,T2))) but got {conclusions[0]}"

                    )


            else:  # Handle other versions if necessary

                print(f"Error: Unsupported version '{version}' for similar_triangle_property_line_ratio.")

                return GeometricError(

                    tier=ErrorTier.TIER1_THEOREM_CALL_SYNTAX_VIOLATION,

                    message=f"Unsupported version {version} for similar_triangle_property_line_ratio",

                    details="Only version 1 is currently implemented with explicit ratio logic."

                )



        elif theorem_name == "triangle_perimeter_formula":


            match = re.search(

                r'Equal\(PerimeterOfTriangle\((\w+)\),Add\(LengthOfLine\((\w+)\),LengthOfLine\((\w+)\),LengthOfLine\((\w+)\)\)\)',

                conclusions[0])

            if match:
                triangle = match.group(1)

                side1 = match.group(2)

                side2 = match.group(3)

                side3 = match.group(4)

                # Create length variables for each side.

                side1_var = self.add_length(side1[0], side1[1])

                side2_var = self.add_length(side2[0], side2[1])

                side3_var = self.add_length(side3[0], side3[1])

                # Calculate the perimeter expression as the sum of side lengths.

                perimeter_expr = side1_var + side2_var + side3_var

                # Create a new Real variable to represent the perimeter of the triangle.

                perimeter_var = Real(f"perimeter_{triangle}")

                # Add the constraint to the solver:

                self.solver.add(perimeter_var == perimeter_expr)

                # Store the variable so that later we can retrieve its value.

                self.triangle_perimeters[triangle] = perimeter_var

                print(
                    f"Added perimeter constraint for triangle {triangle}: {perimeter_var} == {side1_var} + {side2_var} + {side3_var}")


        elif theorem_name == "adjacent_complementary_angle":
            version = args[0]
            if version == "1":
                match = re.search(r'Equal\(Add\(MeasureOfAngle\((\w+)\),\s*MeasureOfAngle\((\w+)\)\),\s*180\)',
                                  conclusions[0])

                if match:
                    # Get angles and normalize them
                    angle1, angle2 = match.group(1), match.group(2)
                    norm_angle1 = self.normalize_angle_name(angle1)
                    norm_angle2 = self.normalize_angle_name(angle2)

                    # Add constraints using normalized angles
                    angle1_var = self.add_angle(norm_angle1[0], norm_angle1[1], norm_angle1[2])
                    angle2_var = self.add_angle(norm_angle2[0], norm_angle2[1], norm_angle2[2])
                    self.solver.add(angle1_var + angle2_var == 180)

                    print(f"Added supplementary relationship: {norm_angle1} + {norm_angle2} = 180")
            elif version == "2":
                print("2")




        elif theorem_name == "line_addition":

            # Match conclusion pattern: Equal(LengthOfLine(CA),Add(LengthOfLine(CD),LengthOfLine(DA)))

            match = re.search(

                r'Equal\(LengthOfLine\((\w+)\),Add\(LengthOfLine\((\w+)\),LengthOfLine\((\w+)\)\)\)',

                conclusions[0]

            )

            if not match:
                return GeometricError(

                    tier=ErrorTier.TIER1_THEOREM_CALL_SYNTAX_VIOLATION,

                    message="Invalid conclusion format for line_addition",

                    details="Expected: Equal(LengthOfLine(total),Add(LengthOfLine(part1),LengthOfLine(part2)))"

                )

            total_line, part1, part2 = match.groups()

            # Create or get length variables for all segments

            total_var = self.add_length(total_line[0], total_line[1])

            part1_var = self.add_length(part1[0], part1[1])

            part2_var = self.add_length(part2[0], part2[1])

            # Add the length addition constraint

            self.solver.add(total_var == part1_var + part2_var)

            print(f"Added line addition constraint: {total_line} = {part1} + {part2}")

            return None




        elif theorem_name == "right_triangle_property_pythagorean":
            version = args[0]
            if version == "1":
                # Expecting a conclusion list like:

                # ["Equal(Add(Pow(LengthOfLine(GH),2),Pow(LengthOfLine(HE),2)),Pow(LengthOfLine(GE),2))"]

                match = re.search(

                    r'Equal\(Add\(Pow\(LengthOfLine\((\w+)\),2\),Pow\(LengthOfLine\((\w+)\),2\)\),Pow\(LengthOfLine\((\w+)\),2\)\)',

                    conclusions[0]

                )

                if match:

                    leg1, leg2, hyp = match.group(1), match.group(2), match.group(3)

                    # Retrieve or create the Z3 length variables for the sides.

                    leg1_var = self.add_length(leg1[0], leg1[1])

                    leg2_var = self.add_length(leg2[0], leg2[1])

                    hyp_var = self.add_length(hyp[0], hyp[1])

                    # Ensure the side lengths are positive.



                    # Add the Pythagorean constraint.

                    self.solver.add(leg1_var * leg1_var + leg2_var * leg2_var == hyp_var * hyp_var)

                    # Optionally, add extra ordering constraints.

                    self.solver.add(leg1_var + leg2_var > hyp_var)

                    self.solver.add(hyp_var > leg1_var, hyp_var > leg2_var)

                    print(f"Added Pythagorean constraint: {leg1}^2 + {leg2}^2 = {hyp}^2")

                else:

                    return GeometricError(

                        tier=ErrorTier.TIER1_THEOREM_CALL_SYNTAX_VIOLATION,

                        message="Conclusion format error for right_triangle_property_pythagorean",

                        details="Expected format: Equal(Add(Pow(LengthOfLine(leg1),2),Pow(LengthOfLine(leg2),2)),Pow(LengthOfLine(hyp),2))"

                    )
            elif version == "2":
                print("2")






        elif theorem_name == "parallel_property_alternate_interior_angle":

            version = args[0]

            if version == "1":

                # Version 1: Use the original behavior.

                m = re.search(r'Equal\(MeasureOfAngle\((\w{3})\),\s*MeasureOfAngle\((\w{3})\)\)', conclusions[0])

                if m:

                    angle1, angle2 = m.group(1), m.group(2)

                    a1 = self.add_angle(angle1[0], angle1[1], angle1[2])

                    a2 = self.add_angle(angle2[0], angle2[1], angle2[2])

                    self.solver.add(a1 == a2)

                    print(f"[Version 1] Added constraint: {angle1} == {angle2}")

                else:

                    return GeometricError(

                        tier=ErrorTier.TIER1_THEOREM_CALL_SYNTAX_VIOLATION,

                        message="Conclusion format error for parallel_property_alternate_interior_angle (version 1)",

                        details="Expected format: Equal(MeasureOfAngle(XXX),MeasureOfAngle(YYY))"

                    )

            elif version == "2":

                # Version 2: For example, expect a different set of angle tokens.

                # In the sample, the conclusion is:

                # "Equal(MeasureOfAngle(GHD),MeasureOfAngle(HGJ))"

                m = re.search(r'Equal\(MeasureOfAngle\((\w{3})\),\s*MeasureOfAngle\((\w{3})\)\)', conclusions[0])

                if m:

                    angle1, angle2 = m.group(1), m.group(2)

                    a1 = self.add_angle(angle1[0], angle1[1], angle1[2])

                    a2 = self.add_angle(angle2[0], angle2[1], angle2[2])

                    self.solver.add(a1 == a2)

                    print(f"[Version 2] Added alternate interior angle constraint: {angle1} == {angle2}")

                else:

                    return GeometricError(

                        tier=ErrorTier.TIER1_THEOREM_CALL_SYNTAX_VIOLATION,

                        message="Conclusion format error for parallel_property_alternate_interior_angle (version 2)",

                        details="Expected format: Equal(MeasureOfAngle(XXX),MeasureOfAngle(YYY))"

                    )


        elif theorem_name == "quadrilateral_property_angle_sum":

            if len(args) < 2:
                return GeometricError(tier=ErrorTier.TIER1_THEOREM_CALL_SYNTAX_VIOLATION,

                                      message="Invalid number of arguments",

                                      details="Expected quadrilateral name")

            quad_name = args[1]

            angle_vars = []

            for i in range(len(quad_name)):
                p1 = quad_name[i]

                p2 = quad_name[(i + 1) % len(quad_name)]

                p3 = quad_name[(i + 2) % len(quad_name)]

                avar = self.add_angle(p1, p2, p3)

                angle_vars.append(avar)

                print(f"Angle at vertex {p2} added for quadrilateral {quad_name}")

            self.solver.add(sum(angle_vars) == 360)

            print("Added quadrilateral angle sum constraint: sum of angles = 360°")



        elif theorem_name == "angle_addition":

            version = args[0]

            if version == "1":
                m = re.search(
                    r'Equal\(MeasureOfAngle\((\w{3})\),\s*Add\(MeasureOfAngle\((\w{3})\),\s*MeasureOfAngle\((\w{3})\)\)\)',
                    conclusions[0])

                if m:

                    sum_angle, angle1, angle2 = m.group(1), m.group(2), m.group(3)

                    sum_var = self.add_angle(sum_angle[0], sum_angle[1], sum_angle[2])

                    angle1_var = self.add_angle(angle1[0], angle1[1], angle1[2])

                    angle2_var = self.add_angle(angle2[0], angle2[1], angle2[2])

                    self.solver.add(sum_var == angle1_var + angle2_var)

                    print(f"Added angle addition constraint: {sum_angle} = {angle1} + {angle2}")

                else:

                    return GeometricError(tier=ErrorTier.TIER1_THEOREM_CALL_SYNTAX_VIOLATION,

                                          message="Conclusion format error for angle_addition",

                                          details="Expected format: Equal(MeasureOfAngle(XXX),Add(MeasureOfAngle(YYY),MeasureOfAngle(ZZZ)))")

                return None
            else:
                return GeometricError(tier=ErrorTier.TIER1_THEOREM_CALL_SYNTAX_VIOLATION,

                                      message="these is no such version for the theorem",

                                      details="these is no such version for the theorem angle_addition")


        constraints_added = self.apply_trig_constraints()
        if constraints_added > 0:
            print(f"Added {constraints_added} trigonometric constraints after theorem {theorem_name}")

        return None  # or return the error if there was one


def get_cyclic_variations_rectangle(para_name: str) -> Set[str]:
    """Return all cyclic variations of a polygon name.
    For instance, "PNML" returns {"PNML", "NMLP", "MLPN", "LPNM"}.
    """
    variations = set()
    n = len(para_name)
    for i in range(n):
        variation = para_name[i:] + para_name[:i]
        variations.add(variation)
    return variations


def get_cyclic_variations(para_name: str) -> Set[str]:
    """Get all cyclic variations of a parallelogram name
    For example, ABCD generates: ABCD, BCDA, CDAB, DABC
    But not reversed versions like DCBA
    """
    variations = set()
    n = len(para_name)
    for i in range(n):
        variations.add(para_name[i:] + para_name[:i])
    return variations


def verify_geometric_proof(filename: str, print_output=True) -> tuple:
    """
    Main function to verify a geometric proof.
    Returns (result, feedback, error_tier) where error_tier is one of:
    - "TIER1_THEOREM_CALL_SYNTAX_VIOLATION" for incorrect theorem calls
    - "TIER2_PREMISE_VIOLATION" for premise violations
    - "TIER3_GOAL_NOT_REACHED" for failures to reach the goal
    - None for successful verifications
    """
    import contextlib
    import sys
    ctx = contextlib.nullcontext() if print_output else contextlib.redirect_stdout(None)
    with ctx:
        try:
            question_match = re.search(r'question[_-]?(\d+)', filename, re.IGNORECASE)
            question_name = f"question_{question_match.group(1)}" if question_match else "unknown_question"
            print(f"Processing {question_name}...")
            with open(filename, 'r') as file:
                content = file.read()

            theorem = GeometricTheorem()
            theorem.question_name = question_name
            result, feedback = theorem.parse_and_verify_proof(content)

            # Extract error tier from feedback if there's a failure
            error_tier = None
            if not result and feedback:
                # Look for specific error tier mentions
                if "Error in TIER1_THEOREM_CALL_SYNTAX_VIOLATION" in feedback:
                    error_tier = ErrorTier.TIER1_THEOREM_CALL_SYNTAX_VIOLATION
                elif "Error in TIER2_PREMISE_VIOLATION" in feedback:
                    error_tier = ErrorTier.TIER2_PREMISE_VIOLATION
                elif "Error in TIER3_GOAL_NOT_REACHED" in feedback:
                    error_tier = ErrorTier.TIER3_GOAL_NOT_REACHED
                # Check for premise error patterns in detailed feedback
                elif feedback.startswith("verification failed.") and (
                        "Missing premise:" in feedback or "- You tried to use theorem:" in feedback):
                    error_tier = ErrorTier.TIER2_PREMISE_VIOLATION
                # Check for goal error patterns in detailed feedback
                elif feedback.startswith("verification failed.") and "- Goal:" in feedback:
                    error_tier = ErrorTier.TIER3_GOAL_NOT_REACHED
                # Default to TIER1 for other errors
                else:
                    error_tier = ErrorTier.TIER1_THEOREM_CALL_SYNTAX_VIOLATION

            print(f"\nOverall verification {'succeeded' if result else 'failed'}")
            return result, feedback, error_tier
        except Exception as e:
            print(f"Error: {str(e)}")
            return False, f"Error: {str(e)}", None


# Modified main section
if __name__ == "__main__":
    result, feedback, error_tier = verify_geometric_proof(
        "/Users/eitanstern/Desktop/orens_code/geometric_verifer/questions/the new format for questions after jan_17/new_45_questions/question_437/question437_gt",print_output=False)

    if not result:
        print(feedback)
    else:
        print("Verification succeeded")