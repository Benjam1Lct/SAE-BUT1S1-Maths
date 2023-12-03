def evaluer_clause(clause,list_var):
    '''Arguments : une liste d'entiers non nuls traduisant une clause,une liste de booléens informant de valeurs logiques connues (ou None dans le cas contraire) pour un ensemble de variables
    Renvoie : None ou booléen
    '''
    if clause == []:
        return False
    else:
        for i in range(len(clause)):
            if clause[i] > 0:
                clause[i] = list_var[abs(clause[i])-1]
            elif list_var[abs(clause[i])-1] == None:
                clause[i] = None
            else:
                clause[i] = not list_var[abs(clause[i])-1]
    
    if True in clause:
        return True
    elif None in clause:
        return None
    else:
        return False
    
'''--------------------------------------------------------------------------------------------------------------------------------'''
    
def retour(list_var,list_chgmts):
    '''
    renvoie :l1,l2 avec :
    l1 : la liste actualisée des valeurs attribuées aux variables 
    l2 : la liste actualisée de l'ensemble des changements effectués depuis une formule initiale
    
    '''
    if not list_chgmts:
        return list_var, list_chgmts

    for change in reversed(list_chgmts):
        if change[1] == True:
            list_var[change[0]] = False
            change[1] = False
            return list_var, list_chgmts
        elif change[1] == False:
            list_var[change[0]] = None
            list_chgmts.remove(change)
            if len(list_chgmts) < 1:
                return list_var, list_chgmts
    return list_var, list_chgmts

'''--------------------------------------------------------------------------------------------------------------------------------'''
    
def progress_simpl_for_dpll(formule,list_var,list_chgmts,list_sans_retour):
    '''Arguments : list_sans_retour contient l'ensemble des numéros de variables auxquelles on a affecté une valeur logique sur laquelle on ne reviendra pas
    renvoie :form,l1,l2,l3 avec :
    form : la formule simplifiée
    l1 : la liste actualisée des valeurs attribuées aux variables après le changement effectué
    l2 : la liste actualisée de l'ensemble des changements effectués
    l3 : la liste éventuellement actualisée des numéros de variables auxquelles une affectation a été attribuée sur laquelle on ne reviendra pas
    '''
    for clause in formule:
        if len(clause) == 1:
            if clause[0] < 0:
                list_var[abs(clause[0]) - 1] = False
                list_chgmts.append([abs(clause[0]) - 1, False])
            else:
                list_var[abs(clause[0]) - 1] = True
                list_chgmts.append([abs(clause[0]) - 1, True])
            list_sans_retour.append(abs(clause[0]) - 1)
            formule = retablir_for(formule, list_chgmts)
            return formule, list_var, list_chgmts, list_sans_retour
    
    content_formule = []
    for clause in formule:
        for value in clause:
            if value not in content_formule:
                content_formule.append(value)
    content_formule = sorted(content_formule)

    for value in content_formule:
        if -(value) in content_formule:
            content_formule.remove(value)
            content_formule.remove(-(value))

    if len(content_formule) > 1:
        formule, list_var, list_chgmts = progress_simpl_for(formule, list_var, list_chgmts)
        return formule, list_var, list_chgmts, list_sans_retour
    else:
        if content_formule[0] < 0:
            list_var[abs(content_formule[0]) - 1] = False
            list_chgmts.append([abs(content_formule[0]) - 1, False])
        else:
            list_var[abs(content_formule[0]) - 1] = True
            list_chgmts.append([abs(content_formule[0]) - 1, True])
        list_sans_retour.append(abs(content_formule[0]) - 1)
        formule = retablir_for(formule, list_chgmts)
        return formule, list_var, list_chgmts, list_sans_retour

'''--------------------------------------------------------------------------------------------------------------------------------'''

def retour_simpl_for_dpll(formule_init,list_var,list_chgmts,list_sans_retour):
    '''
    Renvoie : form,l1,l2,l3
    form : nouvelle formule
    l1 : nouvelle list_var 
    l2 : nouvelle list_chgmts
    l3 : nouvelle list_sans_retour
    '''
    if list_sans_retour == []:
        formule, list_var, list_chgmts = retour_simpl_for(formule_init, list_var, list_chgmts)
        return formule, list_var, list_chgmts, list_sans_retour
    else:
        for clause in reversed(list_chgmts):
            if clause[0] in list_sans_retour:
                list_chgmts.remove(clause)
                list_sans_retour.remove(clause[0])
                list_var[clause[0]] = None
        if list_chgmts != []:
            formule, list_var, list_chgmts = retour_simpl_for(formule_init, list_var, list_chgmts)
            return formule, list_var, list_chgmts, list_sans_retour
        
        return formule_init, list_var, list_chgmts, list_sans_retour

'''--------------------------------------------------------------------------------------------------------------------------------'''

def resol_parcours_arbre(formule_init,list_var,list_chgmts):
    ''' Prend en paramètre : formule_init, list_var, list_chgmts
            formule_init : une liste de listes d'entiers non nuls traduisant une formule,une liste de booléens informant de valeurs logiques connues (ou None dans le cas contraire) pour un ensemble de variables
            list_var : une liste de booléens informant de valeurs logiques connues
            list_chgmts : une liste de listes d'entiers non nuls traduisant une formule,une liste de booléens informant de valeurs logiques connues (ou None dans le cas contraire) pour un ensemble de variables
        Renvoie : SAT,l1
            SAT : booléen indiquant la satisfiabilité de la formule
            l1 : une liste de valuations rendant la formule vraie ou une liste vide
    '''
    if evaluer_cnf(formule_init,list_var):
        return True, list_var
    elif list_chgmts == []:
        return False, []
    else:
        test_list_var, test_list_chgmts = copy.deepcopy(list_var), copy.deepcopy(list_chgmts)
        test_list_var, test_list_chgmts = progress(test_list_var, test_list_chgmts)
        if (test_list_var, test_list_chgmts) == (list_var, list_chgmts):
            list_var, list_chgmts = retour(list_var, list_chgmts)
            return resol_parcours_arbre(formule_init, list_var, list_chgmts)
        else:
            list_var, list_chgmts = progress(test_list_var, test_list_chgmts)
            return resol_parcours_arbre(formule_init, list_var, list_chgmts)

'''--------------------------------------------------------------------------------------------------------------------------------'''

def resol_parcours_arbre_simpl_for(formule_init,formule,list_var,list_chgmts):#la même distinction peut être faite entre formule et formule_init
    '''
    Renvoie SAT,l1 avec :
    SAT=True ou False
    l1=une liste de valuations rendant la formule vraie ou une liste vide
    '''
    '''
    print('valuation=',list_var)
    print('changement=',list_chgmts)
    print('formule=',formule)
    print('')
    '''

    #Initialisation du parcours
    if list_chgmts==[]:
        if [] in formule:
            return False,[]
        if formule==[]:
            return True,list_var
        form,list_var_init,list_chgmts_init=progress_simpl_for(formule,list_var,[])
        return resol_parcours_arbre_simpl_for(formule_init,form,list_var_init,list_chgmts_init)
    #Reste du parcours à implémenter :
    if formule == []:
        list_chgmts = []
    test = True
    for changements in list_chgmts:
        if changements[1] != False:
            test = False
    if test and len(list_chgmts) > 0:
        if list_chgmts[0][0] == 0:
            return resol_parcours_arbre_simpl_for(formule_init,[[]],list_var,[])
    if [] in formule:
        if len(list_chgmts) == 1 and list_chgmts[0][1] == False:
            return resol_parcours_arbre_simpl_for(formule_init,formule,list_var,[])
        else:
            _,list_var,list_chgmts=retour_simpl_for(formule,list_var,list_chgmts)
            formule = copy.deepcopy(formule_init)
            formule = init_formule_simpl_for(formule, list_var)
    else:
        formule,list_var,list_chgmts=progress_simpl_for(formule,list_var,list_chgmts)
        if formule == []:
            list_chgmts = []
    return resol_parcours_arbre_simpl_for(formule_init,formule,list_var,list_chgmts)

'''--------------------------------------------------------------------------------------------------------------------------------'''

def resol_parcours_arbre_simpl_for_dpll(formule_init,formule,list_var,list_chgmts,list_sans_retour):
    '''
    Renvoie SAT,l1 avec :
SAT=True ou False
l1=une liste de valuations rendant la formule vraie ou une liste vide
'''
    #Initialisation du parcours
    if list_chgmts==[]:
        if [] in formule:
            return False,[]
        if formule==[]:
            return True,list_var
        form,list_var_init,list_chgmts_init,list_sans_retour_init=progress_simpl_for_dpll(formule,list_var,[],[])
        return resol_parcours_arbre_simpl_for_dpll(formule_init,form,list_var_init,list_chgmts_init,list_sans_retour_init)
    #Reste du parcours à implémenter :
    if formule == []:
        list_chgmts = []
    test = True
    for changements in list_chgmts:
        if changements[1] != False:
            test = False
    if test and len(list_chgmts) > 0:
        if list_chgmts[0][0] == 0:
            #print('p7',formule, list_var, list_chgmts)
            return resol_parcours_arbre_simpl_for(formule_init,[[]],list_var,[],list_sans_retour)
    if [] in formule:
        if len(list_chgmts) == 1 and list_chgmts[0][1] == False or len(list_chgmts) == len(list_sans_retour):
            return resol_parcours_arbre_simpl_for_dpll(formule_init,formule,list_var,[],list_sans_retour)
        else:   
            formule,list_var,list_chgmts, list_sans_retour = retour_simpl_for_dpll(formule,list_var,list_chgmts, list_sans_retour)
            formule = copy.deepcopy(formule_init)
            formule = init_formule_simpl_for(formule, list_var)
    else:
        formule,list_var,list_chgmts, list_sans_retour = progress_simpl_for_dpll(formule,list_var,list_chgmts, list_sans_retour)
        if formule == []:
            list_chgmts = []
    return resol_parcours_arbre_simpl_for_dpll(formule_init,formule,list_var,list_chgmts, list_sans_retour)

