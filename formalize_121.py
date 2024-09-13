from z3 import *

# Define some operators we may use in these calculations.

def excess_of(x, y):
    return If(x > y, x - y, 0)

def lesser_of(x, y):
    return If(x < y, x, y)

def greater_of(x, y):
    return If(x > y, x, y)

# We are going to look for (1) the maximum amount that can be excluded under Section 121,
# for (2) two spouses, who are (3) filing jointly, who both (4) moved for a "good reason,"
# amd who for some reason (5) do not qualify for the full $500,000 limitation.
# This does *not* check for the amount of gain or the amount of the exclusion;
# this is looking for the "limitation."

def verify_121_limitation_branch(determinemarried, timeperiod='years'):
    # optimizer to allow soft constraints
    s = Optimize()

    ## Defining relevant variables

    # Length of time each spouse used and owned the property, and when they previously sold it;
    # in terms of years. We can check for years, months, or days. The regulations say
    # months (24) or days (730) is fine. 1.121-3(g)(1). Spouses are S1 and S2.
    OwnedS1, OwnedS2, UsedS1, UsedS2, PreviousSaleS1, PreviousSaleS2 = Ints('OwnedS1 OwnedS1 UsedS1 UsedS2 PreviousSaleS1 PreviousSaleS2')
    variables = [OwnedS1, OwnedS2, UsedS1, UsedS2, PreviousSaleS1, PreviousSaleS2]
    

    # allowing the denominator to be years, even though only months or days are allowed,
    # because the "years" answer may give a helpfully intuitive response
    denom_dict = {'years':1,'months':12,'days':365}

    relevant_denom = 2*denom_dict[timeperiod]
    

    # all these periods must be nonnegative, plus adding soft constraints to make the answers more readable
    for i,var in enumerate(variables):
        s.add(var >= 0)
        s.add_soft(var > denom_dict[timeperiod],1,f"lower_bound{i}")
        s.add_soft(var < 4 * denom_dict[timeperiod],1,f"upper_bound{i}")

    

    # Assume that everyone has a good reason for moving, so that the sliding scale of 121(c) applies  
    ReasonMoveS1 = True
    ReasonMoveS2 = True
    ReasonMoveCouple = True

    # the statutory limitation for single, under 121(b)(1)
    single_limitation = 250000

    # the maximum married limitation, under 121(b)(2); additional
    # requirements will have to be met for this to apply
    married_limitation = 500000

    # define what it means for a particular number to "meet requirements." This is
    # based on the language of the statute. 121(a): "Gross income shall not include gain 
    # from the sale or exchange of property if, during the 5-year period ending on the 
    # date of the sale or exchange, such property has been owned and used by the taxpayer
    # as the taxpayer’s principal residence for periods aggregating 2 years or more." 
    # 121(b)(3): "Subsection (a) shall not apply to any sale or exchange by the taxpayer 
    # if, during the 2-year period ending on the date of such sale or exchange, there was
    # any other sale or exchange by the taxpayer to which subsection (a) applied." 

    def meets(lengthtocheck):
        return If(lengthtocheck >= relevant_denom,True,False)

    ## There are two paths: the "Sum Limitation" path and the "121(c)" path

    ## Sum Limitation Path

    # 121(b)(2)(A) - this is when the $500,000 limitation applies.
    # (Intro) All three of these requirements must be met, thus the initial "And"
    # 121(b)(2)(A)(i):  Or(meets(OwnedS1),meets(OwnedS2)):  either spouse meets ownership
    # 121(b)(2)(A)(ii): And(meets(UsedS1),meets(UsedS2)): both spouses meet use
    # 121(b)(2)(A)(iii):Not(Or(Not(meets(PreviousSaleS1)),Not(meets(PreviousSaleS2)))): neither spouse fails previous sale;
    # this not/or/not is to match the statute "neither spouse is ineligible"

    married_limitation_conditions = And(
                                    Or(meets(OwnedS1),meets(OwnedS2)),
                                    And(meets(UsedS1),meets(UsedS2)),
                                    Not(Or(Not(meets(PreviousSaleS1)),Not(meets(PreviousSaleS2))))
                                    )

    # forcing them not to qualify for the full married limitation conditions
    married_limitation_conditions_fail = Not(married_limitation_conditions)

    s.add(married_limitation_conditions_fail)

    # Section 121 calculation has to be defined here, because to determine the sum limitation,
    # we need to know Section 121 calculation
    # "the amount which bears the same ratio to such limitation as the shorter of [relevant length]
    # bears to 2 years" is x/limitation = relevant length/2. However, "[t]he denominator of the 
    # fraction is 730 days or 24 months (depending on the measure of time used in the numerator)."  
    # Therefore say relevantlength*multiplier, where multiplier is determined by dividing 1 by the 
    # relevant denominator.

    multiplier = RealVal(1) / RealVal(relevant_denom)

    def create_121_c(reasonmove,limitationtouse,relevantlength):
        return If(reasonmove,limitationtouse * (relevantlength*multiplier),RealVal(0))

    # 1.121-3(g): "The numerator of the fraction is the shortest of the period of time
    # that the taxpayer owned the property...; the period of time that the taxpayer used the
    # property as the taxpayer's principal residence...; or the period of time between the
    # date of a prior sale or exchange of property for which the taxpayer excluded gain...."

    # Each spouse is treated as owning the property during the period either spouse owned property
    # For now, let's say relevant ownership is the greater of the two ownership periods, but that's not
    # exactly right, because there could be periods where each of them owns it individually, plus
    # an overlap period.

    either_ownership_length = greater_of(OwnedS1,OwnedS2)

    relevantlength_spouse_1  =  lesser_of(either_ownership_length,lesser_of(UsedS1,PreviousSaleS1))
    relevantlength_spouse_2  =  lesser_of(either_ownership_length,lesser_of(UsedS2,PreviousSaleS2))

    S1_121 = create_121_c(ReasonMoveS1,single_limitation,relevantlength_spouse_1)
    S2_121 = create_121_c(ReasonMoveS2,single_limitation,relevantlength_spouse_2)

    sum_limitation = S1_121 + S2_121

    SumLimitation = If(married_limitation_conditions,married_limitation,sum_limitation)

    ## 121(c) path

    # 121(c)(2): when 121(c) applies. This says that 121(c) applies only if both spouses
    # fail to meet ownership requirements; because of 121(d), either person meeting it
    # will count as successful; this is not consistent with 121(b)(2), because there,
    # both spouses must meet the use requirement. So maybe the situation we are looking for
    # is that one spouse meets use and ownership (so that (a) applies), but the other
    # spouse does not meet use? Not clear from the statute.
    successful_ownership_use = Or(
                                    And(meets(UsedS1),meets(OwnedS1)),
                                    And(meets(UsedS2),meets(OwnedS2))
                                    )

    # successful previous sale; this is a genuine question and I'm not sure
    # what this would mean. Here I've said that
    # they both have to succeed for this to succeed 

    # “if a single taxpayer who is otherwise eligible for an exclusion marries someone
    # who has used the exclusion within the two years prior to the marriage, the bill
    # would allow the newly married taxpayer a maximum exclusion of $250,000. Once both spouses
    # satisfy the eligibility rules and two years have passed since the last exclusion was
    # allowed to either of them, the taxpayers may exclude $500,000 of gain on their joint return.”
    # Source: H Rept No. 105-148 (PL 105-34) p. 348.
    
    successful_previous_sale = And(meets(PreviousSaleS1),meets(PreviousSaleS2))

    # section 121(c) applies if they fail one of these
    section_121_c_conditions_fail = Or(Not(successful_ownership_use),Not(successful_previous_sale))

    # force Section 121(c) to be triggered
    s.add(section_121_c_conditions_fail)

    # what is the relevant length of ownership, use, and previous sale if the couple is married?
    # three options: maximum, minimum, average. The program checks all three of these possibilities.
    minimum_length = lesser_of(relevantlength_spouse_1,relevantlength_spouse_2)
    maximum_length = greater_of(relevantlength_spouse_1,relevantlength_spouse_2)
    average_length =(relevantlength_spouse_1+relevantlength_spouse_2)*.5

    length_dict = {'maximum':maximum_length,'minimum':minimum_length,'average':average_length}

    relevant_length_married = length_dict[determinemarried]

    married_121_c = create_121_c(ReasonMoveCouple,married_limitation,relevant_length_married)

    Section121cLimitation = If(section_121_c_conditions_fail,married_121_c,married_limitation)

    # This is kind of a side note, but notice that thm1 is false and thm2 is true. This is because
    # the requirement for (b)(2) is actually stricter: If one spouse meets ownership and use, that 
    # is not enough; the other spouse must also meet use. In 121(c), in contrast, it appears that
    # one spouse meeting ownership and use is enough, because of 121(d)(1).
    thm1 = Implies(married_limitation_conditions_fail,section_121_c_conditions_fail)
    thm2 = Implies(section_121_c_conditions_fail,married_limitation_conditions_fail)
    

    ### Now check to see whether the Sum Limitation is always equal to the 121(c) limitation
    ### Assert that they are not equal and look for a model where this is true.
    s.add(SumLimitation != Section121cLimitation)
    result = s.check()
    if result == sat:
        model = s.model()

        list_variables = [SumLimitation,Section121cLimitation,S1_121,S2_121]
        eval_variables = [float(model.eval(x).numerator_as_long())/float(model.eval(x).denominator_as_long()) for x in list_variables]
        string_variables = ["${:,.0f}".format(x) for x in eval_variables]

        formatted_dict = dict(zip(list_variables,string_variables))

        return f"Checking the equivalence using the {determinemarried} of the two relevant lengths, these two values are not always equal to each other. A model in which they are not equal is\n{model}\nThis model results in a sum limitation of {formatted_dict[SumLimitation]}, with a limitation for Spouse1 of {formatted_dict[S1_121]} and a limitation for Spouse2 of {formatted_dict[S2_121]}. The relevant length for Spouse1 is {model.eval(relevantlength_spouse_1)}, and the relevant length for Spouse2 is {model.eval(relevantlength_spouse_2)}.\nThis model results in a 121(c) limitation of {formatted_dict[Section121cLimitation]}. The relevant length for married is {model.eval(relevant_length_married)}.\n\n\n"

    else:
        return f"Checking the equivalence using the {determinemarried} of the two relevant lengths, SumLimitation and Section121CLimitation are always equal.\n\n\n"

def check_all_lengths(filename = "checkallunits.txt"):
    units_list = ['days','months','years']
    length_list = ['maximum','minimum','average']
    with open(filename, "w") as file:
        for timeperiod in units_list:
            file.write(f"Checking using the units of {timeperiod}:\n\n".upper())
            for length_to_check in length_list:
                file.write(verify_121_limitation_branch(length_to_check,timeperiod=timeperiod))


check_all_lengths()

