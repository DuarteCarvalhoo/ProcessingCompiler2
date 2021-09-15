#include "arvoreAST.h"
#include <windows.h>  
#include <GL/glut.h> 
#include <GL/freeglut.h>
#include <math.h>
#include <semaphore.h>
#define DEG2RAD 3.14159/180.0
//posso usar a root, como variavel global
int flag = 0;
int wightSize = 100;
int hightSize = 100;
float fillRed = 255; //inicializar a 255
float fillGreen = 255;
float fillBlue = 255;
int flagSetup = 0;
int defaultLineWidth = 1;
int strokeFlag = 1;
float strokeRed, strokeGreen, strokeBlue;
boolean paused = FALSE;
int firstFlag =1;
int z=1;
int t=0;
int f=0;
int u=0;
int switchDraw;
int setupAux;
int ifAux;
char highlightType[100];
char highlightChange[100];
float highlightChangeFloat[6];
char highlightChangeOne[100];
char highlightChangeTwo[100];
char highlightChangeThree[100];
char highlightChangeFour[100];
char highlightChangeFive[100];
char highlightChangeSix[100];
char auxEq[100];

int varFlag = 0;
int varCount = 3;
struct varInt *dict;
struct varInt *first;
int flagIf = 0;
int flagVar = 0;
int flagIfTwoArguments = 0;
int flagUseThree = 0;
int flagFirst = 0;
int flagLast = 0;
boolean ifTrue = TRUE;
int firstIf = 0;

extern int num_linha;
int replyZ;
int lastReplyZ;

int begin;
int flagForward = 1;
int flagFor = 0;
int forAux;
int flagFirstFor=0;
char startFor[100];
struct varInt* forPointer;

int flagForForIf = 0;

void display();
void display2();
void display3();
void myMouseHandler(int button, int state, int x, int y);
float checkVar(struct no *varAux);
//void timer(int value);
boolean ifValue(struct no *neto);
void varIntForFunc(struct no *neto);
void auxFor(struct no* decision, struct no* step);
void auxForDo(struct no* step);
//void varDeclFunc(struct no *neto);
//void idle();

void tabela_de_simbolos(struct no *root){
    dict = (struct varInt*) malloc(sizeof(varInt));
    first = (struct varInt*) malloc(sizeof(varInt));
    for(int i=0; i<root->num_filhos;i++){
        printf("%d\n",root->num_filhos);
        printf("new i = %d\n", i);
        printf("root %s\n", root->filhos[i]);
        
        struct no *filho = root->filhos[i];
        if(strcmp(filho->tipo,"MethodDecl")==0){
            //printf("here\n");
            decl_func(filho);
        }
        else if(strcmp(filho->tipo,"Begin")==0){
            //printf("here1\n");
            decl_func(filho);
        }
        else if(strcmp(filho->tipo,"VarDecl")==0){
            printf("here3\n");
            decl_field(filho);
        }
        else{
            printf("o que é --->>> %s\n", filho->tipo);    
        }
    }
}

void decl_func(no* no){
    
    
    char *nome_return;
    char *func_id;
    struct no *entrada_Metodo = no->filhos[0];
    nome_return = (char *) malloc(sizeof(char) * (strlen(entrada_Metodo->tipo)+1));
    strcpy(nome_return, entrada_Metodo->tipo);

    if(strcmp(no->tipo,"MethodDecl")==0){
        entrada_Metodo = no->filhos[1];
    }
    
    func_id = (char *) malloc(sizeof(char)*(strlen(entrada_Metodo->valor)+1));
    strcpy(func_id, entrada_Metodo->valor);

    //printf("func -> %s, return -> %s\n", func_id, nome_return);

    
    elementos_tabela *novo_elemento = cria_funcdecl(func_id, nome_return, entrada_Metodo->linha, entrada_Metodo->coluna);

    //ver se pode ser null ou nao -> entrada_Metedo->filhos[2]
    //printf("se %s -> %d\n", func_id, no->num_filhos);
    struct no *parametros_metodo = entrada_Metodo;
    if(parametros_metodo != NULL){
        printf("parametros: tipo %s valor %s", parametros_metodo->tipo, parametros_metodo->valor);
        for(int i=0; i<parametros_metodo->num_filhos; i++){
            (novo_elemento->funcdecl->n_parametros)++;
            (novo_elemento->funcdecl->n_parametros_entrada)++;
            struct no *parametros = parametros_metodo->filhos[i];
            char *var = (char *) malloc(sizeof(char) * (strlen(parametros->filhos[0]->tipo)+1));
            strcpy(var, parametros->filhos[0]->tipo);
            printf("valor -> %s\n",parametros->filhos[1]->valor);
            inserir_vardecl(parametros->filhos[1]->valor, var, "parametro", &(novo_elemento->funcdecl->variaveis), parametros->filhos[1]->linha, parametros->filhos[1]->coluna);
            free(var);
        }
    }    
    
    //printf("here1\n");
    
    elementos_tabela *aux = tabela_global;

    while (aux != NULL)
    {  
        elementos_tabela *nood = procurar_elementos(func_id, aux);
        if(nood != NULL){
            if(nood->tipo_decl == novo_elemento->tipo_decl){
                if(strcmp(nood->funcdecl->tipo_return, novo_elemento->funcdecl->tipo_return)==0){
                    if(nood->funcdecl->n_parametros_entrada == novo_elemento->funcdecl->n_parametros_entrada){
                        elementos_tabela *var_nood = nood->funcdecl->variaveis;
                        elementos_tabela *var_aux = novo_elemento->funcdecl->variaveis;
                        int n_parametros_iguais = 0;
                        for(int i=0; i<nood->funcdecl->n_parametros_entrada;i++){
                            if(strcmp(var_nood->vardecl->tipo, var_aux->vardecl->tipo)==0){
                                n_parametros_iguais++;
                            }
                            var_nood = var_nood->next;
                            var_aux = var_aux->next;
                        }
                        if(n_parametros_iguais==nood->funcdecl->n_parametros_entrada){
                            novo_elemento->repetido = 1;
                            break;
                        }
                    }
                }
            }
            if(nood->tipo_decl == 2){
                if(strcmp(novo_elemento->id, nood->id)==0){
                    if(strcmp(novo_elemento->id, "_")==0){
                        novo_elemento->repetido =1;
                        printf("Linha %d, coluna %d: Simbolo %s(", novo_elemento->linha, novo_elemento->coluna, novo_elemento->id);
                        elementos_tabela *aux_var = novo_elemento->funcdecl->variaveis;
                        for(int i=0; i<novo_elemento->funcdecl->n_parametros_entrada;i++){
                            printf("%s", aux_var->vardecl->tipo);
                            if(i==novo_elemento->funcdecl->n_parametros_entrada-1){
                                printf(",");
                            }
                            aux_var = aux_var->next;
                        }
                        printf(") já foram definidos\n");
                        break;
                    }
                }
            }
        }
        aux = aux->next;
    }
    inserir_func(novo_elemento, &tabela_global);
    //printf("here2\n");
    struct no *body_Metodo = no->filhos[1];
    //printf("tipo %s, valor %s\n",body_Metodo->tipo, body_Metodo->valor);
    for(int i=1;i<no->num_filhos;i++){
        if(strcmp(no->filhos[i]->tipo, "VarDecl")==0){
            struct varInt *auxVar = (struct varInt*) malloc(sizeof(varInt));
            //printf("vardecl valor: %s\n", no->filhos[i]->filhos[1]->valor);
            char *var = (char *) malloc(sizeof(char)*(strlen(no->filhos[i]->filhos[0]->tipo)+1));
            strcpy(var, no->filhos[i]->filhos[0]->tipo);
            //printf("teste erro %s\n", no->filhos[i]->filhos[1]->valor);
            auxVar->id = no->filhos[i]->filhos[1]->valor;
            auxVar->tipoVariavel = (char *) malloc(sizeof(char)*(strlen(var)+1));
            strcpy(auxVar->tipoVariavel,var);
            printf("\nteste erro %s\n", var);
            if(strcmp(var,"Color")==0){
                int colorRed = atoi(no->filhos[i]->filhos[2]->filhos[0]->filhos[0]->filhos[0]->valor);
                int colorGreen = atoi(no->filhos[i]->filhos[2]->filhos[0]->filhos[0]->filhos[1]->valor);
                int colorBlue = atoi(no->filhos[i]->filhos[2]->filhos[0]->filhos[1]->valor);
                //float colorFloatAux = (colorBlue+colorGreen+colorRed)/3;
                //printf("color float value %f\n", colorFloatAux);
                printf("here\n");
                char bufFloat[200];
                char finalColor[200];
                sprintf(bufFloat,"%d",colorRed);
                printf("here1\n");
                strcpy(finalColor, bufFloat);
                sprintf(bufFloat,"%d",colorGreen);
                strcat(finalColor, ",");
                strcat(finalColor, bufFloat);
                printf("here2\n");
                sprintf(bufFloat,"%d",colorBlue);
                strcat(finalColor, ",");
                strcat(finalColor, bufFloat);
                printf("finalcolor %s\n",finalColor);
                auxVar->valor = (char *) malloc(sizeof(char)*(strlen(finalColor)+1));
                strcpy(auxVar->valor, finalColor);
                //auxVar->valor = finalColor;
                //printf("color value %s\n", auxVar->valor);
                //printf("color value %s\n", finalColor);
                //printf("color value %s\n", bufFloat);
                
            }else{
                auxVar->valor = no->filhos[i]->filhos[2]->valor;
                //printf("non color value %s\n", auxVar->valor);
            }
            auxVar->next = NULL;
            //printf("value depois do next %s\n", auxVar->valor);
            if(varFlag==0){
                printf("1st time^\n");
                varFlag=1;
                dict = auxVar;
                first = dict;
                //printf("id do first %s\n",first->id);
            }else{
                varCount++;
                printf("seconds\n");
                dict->next = auxVar;
                //printf("seconds half\n");
                dict = dict->next;
                //printf("id do next %s\n",dict->id);
                //printf("value do next %s\n",dict->valor);
            }
            if(procurar_repetidos(no->filhos[i]->filhos[1]->valor, novo_elemento->funcdecl->variaveis, novo_elemento->funcdecl->n_parametros,0)==NULL){
                inserir_vardecl(no->filhos[i]->filhos[1]->valor, var, "null", &(novo_elemento->funcdecl->variaveis), no->filhos[i]->filhos[1]->linha, no->filhos[i]->filhos[1]->coluna);
                (novo_elemento->funcdecl->n_parametros)++;
                //printf("id do erro %s\n", no->filhos[i]->filhos[1]->valor);
                //printf("filho 1 linha %d\n",no->filhos[i]->filhos[1]->linha);
                //printf("filho 1 coluna %d\n",no->filhos[i]->filhos[1]->coluna);
            }
            //printf("id do next %s\n",dict->id);
            //printf("value do next %s\n",dict->valor);
            //printf("tipo de var do next %s\n",dict->tipoVariavel);
            free(var);
        } else if(strcmp(no->filhos[i]->tipo, "MethodDecl")==0){
            //printf("methoddecl valor: %s\n", no->filhos[i]->filhos[0]->valor);
            (novo_elemento->funcdecl->n_parametros)++;
            char *valor = (char *) malloc(sizeof(char)*(strlen(no->filhos[i]->filhos[0]->valor)+1));
            strcpy(valor, no->filhos[i]->filhos[0]->valor);
            inserir_func(cria_funcdecl(valor, "void", no->filhos[i]->filhos[0]->linha, no->filhos[i]->filhos[0]->coluna),&(novo_elemento->funcdecl->variaveis));
            free(valor);
        } else if (strcmp(no->filhos[i]->tipo, "VarAssign")==0){ 
            //AQUI NAO ESTA A FUNCIONAR RESOLVER SEGUNDA FEIRA
            struct varInt *temp2 = (struct varInt*) malloc(sizeof(varInt));
            //Não funciona para assignmente com virgulas tipo "a=0, b=10, c=100"
            struct no *auxFilho = no->filhos[i]->filhos[0];
            //struct no *auxWhile = auxFilho->filhos[1]->filhos[0];
            printf("varAssing auxFilho -> %s\n", auxFilho->tipo);
            //printf("varAssing auxWhile -> %s\n", auxWhile);
            /*if(auxWhile!=NULL){
                while (strcmp(auxFilho->filhos[1]->tipo,auxWhile->tipo)==0){
                    auxCount++;
                    auxWhile = auxFilho->filhos[1]->filhos[auxCount];
                }
            }*/
            temp2 = first;
            for(int u=0;u<auxFilho->num_filhos;u++){
                printf("valor da var assign -> %s\n",auxFilho->filhos[0]->valor);
                printf("vars da funções %s\n", novo_elemento->id);
                if(procurar_elementos(auxFilho->filhos[0]->valor, tabela_global)!=NULL || procurar_elementos(auxFilho->filhos[0]->valor,novo_elemento->funcdecl->variaveis)!=NULL){
                    printf("aqui está tudo bem\n");
                }else{
                    printf("Aqui a variavel em questão nao foi declarada ou o tipo nao coencide \n");
                }
                while(temp2!=NULL){
                    if(strcmp(temp2->id,auxFilho->filhos[0]->valor)==0){
                        temp2->valor=auxFilho->filhos[1]->valor;
                        
                    }
                    temp2 = temp2->next;
                }
            }
        } else{ //if, calls, whiles, etc
            continue;
        }
    }
    free(func_id);
    free(nome_return);
}

void decl_field(no* no){
    char *tipo = (char *) malloc(sizeof(char)*(strlen(no->filhos[0]->tipo)+1));
    strcpy(tipo, no->filhos[0]->tipo);
    char *valor = (char*) malloc(sizeof(char)*(strlen(no->filhos[1]->valor)+1));
    strcpy(valor, no->filhos[1]->valor);
    elementos_tabela *novo_elemento =inserir_decls(valor, tipo, "null", no->filhos[1]->linha, no->filhos[1]->coluna);
    if(no->filhos[2] != NULL){
        printf("filho2!=NULL -> %s\n", no->filhos[2]->valor);
        printf("filho2!=NULLtipo -> %s\n", no->filhos[2]->tipo);
        if(strcmp(no->filhos[2]->tipo,"Virgula")==0 && no->filhos[2]->num_filhos>0){
            int contaVirgulas =1;
            struct no *no_aux=no->filhos[2];
            struct no *no_aux2=no->filhos[2];
            while (strcmp(no_aux->filhos[0]->tipo,"Virgula")==0)
            {
                no_aux=no_aux->filhos[0];
                contaVirgulas++;
            }
            for(int i=0;i<contaVirgulas;i++){
                char *valor2 = (char*) malloc(sizeof(char)*(strlen(no_aux2->filhos[1]->filhos[0]->valor)+1));
                strcpy(valor2, no_aux2->filhos[1]->filhos[0]->valor);
                elementos_tabela *novo_elemento1 = inserir_decls(valor2, tipo, "null", no_aux2->filhos[1]->filhos[0]->linha, no_aux2->filhos[1]->filhos[0]->coluna);
                inserir_func(novo_elemento1, &tabela_global);
                no_aux2 = no_aux2->filhos[0];
            } 
        }
    }
    
    elementos_tabela *aux = tabela_global;

    while (aux !=NULL)
    {
        elementos_tabela *nood =procurar_elementos(novo_elemento->id, aux);
        if(nood!=NULL){
            if(nood->tipo_decl == novo_elemento->tipo_decl){
                if(strcmp(novo_elemento->id, "_")==0){
                    novo_elemento->repetido =1;
                    printf("Linha %d, coluna, %d: Simbolo: %s está reservado.\n", no->filhos[1]->linha, no->filhos[1]->coluna, no->filhos[1]->valor);
                    break;
                }
                novo_elemento->repetido =1;
                printf("Linha %d, coluna, %d: Simbolo: %s está definido.\n", no->filhos[1]->linha, no->filhos[1]->coluna, no->filhos[1]->valor); 
                break;
            }
        }
        aux = aux->next;
    }
    if (strcmp(novo_elemento->id,"_")==0 && novo_elemento->repetido == 0){
        novo_elemento->repetido =1;
        printf("Linha %d, coluna %d: Simbolo %s está reservado\n", novo_elemento->linha, novo_elemento->coluna, novo_elemento->id);
    }
    inserir_func(novo_elemento, &tabela_global);
    free(tipo);
    free(valor);
}

struct no *criar(char* tipo, char* valor, int linha, int coluna){
    //printf("---treeCriar---");
    struct no* new = (struct no *) malloc(sizeof(no));
    if(new == NULL){
        return NULL;
    }
    new->tipo = tipo;
    new->valor = valor;
    new->pai = NULL;
    new->bros = NULL;
    new->num_filhos = 0;
    new->linha = linha;
    new->coluna = coluna;
    return new;
}

struct no *filho(struct no* pai, struct no* filho){
    //printf("---treeFilho---");
    if(pai == NULL || filho == NULL){
        return NULL;
    }
    pai->filhos[pai->num_filhos] = filho;
    pai->num_filhos++;
    filho->pai = pai;
    struct no *temp = filho->bros;
    while(temp != NULL){
        temp->pai = pai;
        pai->filhos[pai->num_filhos] = temp;
        pai->num_filhos++;
        temp = temp->bros;
    }
    
    return pai;
}

struct no *add_bro(struct no* aux, struct no* aux1){
    //printf("---treeBro---");
    struct no *temp = aux;
    if(temp != NULL){
        while(temp->bros != NULL){
            temp = temp->bros;
        }
        temp->bros = aux1;
    }
    return aux;
}

void imprimir(struct no* root1, int profundidade){
    
    if(root1 == NULL){
        //printf("---treeImprimir---");
        return;
    }
    for(int i=0; i<profundidade; i++){
        printf("--");
    }
    if(strcmp(root1->valor, "")==0){
        printf("%s\n", root1->tipo);
    } else {
        printf("%s %s\n", root1->tipo, root1->valor);
    }
    for(int j=0;j<root1->num_filhos;j++){
        imprimir(root1->filhos[j], profundidade+1);
    }
    

    free(root1);

    //fazer um com que este codigo executa so uma vez
    if(flag==0){
        flag = 1;
        int my_argc = 0;
        glutInit( &my_argc, NULL );
        glutCreateWindow("OpenGL draws"); // Create a window with the given title
        init();

        glutInitWindowPosition(50, 50);
        glutReshapeWindow(wightSize*2, hightSize);
        gluOrtho2D(0,wightSize*2,hightSize,0);
        glutDisplayFunc(display);
        //glutIdleFunc(idle);
        glutMouseFunc(myMouseHandler);
        

        //segunda janela
        //glutCreateWindow("Janela de variaveis");
        //glutInitWindowPosition(200,200);
        //glutReshapeWindow(250, 200);
        //gluOrtho2D(0,250,100,0);
        //glutDisplayFunc(display2);
        //glutTimerFunc(1,timer,0);
        //glviewport();
        
        glutMainLoop();
    }
    // ate aqui
}

/*void timer(int value) {
    glutPostRedisplay();
    glutTimerFunc(1,timer,0);
}*/

void init() {
    //tamanho da janela e outras variveis necessárias.
    struct no *initAux = root;
    for(int i=0; i<root->num_filhos;i++){
        struct no *filhoInit = initAux->filhos[i];
        if(strcmp(filhoInit->tipo,"Begin")==0){
            if(strcmp(filhoInit->filhos[0]->valor,"setup")==0){
                struct no* netoInit;
                for(int j=1;j<filhoInit->num_filhos;j++){
                    netoInit = filhoInit->filhos[j];
                    if(strcmp(netoInit->tipo,"MethodDecl")==0){
                        if(strcmp(netoInit->filhos[0]->valor,"size")==0){
                            //codigo do size
                            wightSize = checkVar(netoInit->filhos[1]->filhos[0]);
                            hightSize = checkVar(netoInit->filhos[1]->filhos[1]);
                        }
                    }
                }
            }
        }
    }
}

void display() {
    //printf("display\n");
    //os metodos primitivos, movimentos de rato e teclado
    //fazer os botoes aqui tb
    //os ifs terao de ser aqui
    //background, fills, strokes
    //usar a forma da tabela de simbolos
    /*glViewport(0,0,wightSize,hightSize);
    glMatrixMode(GL_PROJECTION);
	glLoadIdentity();
*/
    glViewport(0,0,wightSize*2,hightSize);

    for(int i=0; i<root->num_filhos;i++){
        struct no *filho = root->filhos[i];
        if(strcmp(filho->tipo,"Begin")==0){
            if(strcmp(filho->filhos[0]->valor,"setup")==0 && flagSetup==0){
                flagSetup = 1;
                //xprintf("Dentro do setup\n");
                //tenho de meter tudo ca dentro agora?  
                struct no *neto;
                //switchSetup = filho->num_filhos;
                //if(u>0 && u<filho->num_filhos){
                setupAux = filho->num_filhos;
                for(int u=1;u<filho->num_filhos;u++){
                    neto = filho->filhos[u];
                    //printf("in setup\n");
                    if(strcmp(neto->tipo,"MethodDecl")==0){
                        if(strcmp(neto->filhos[0]->valor,"background")==0){
                            //codigo do background
                            background(neto);
                        }
                        else if(strcmp(neto->filhos[0]->valor,"fill")==0){
                            //codigo do fill
                            fill(neto);
                        } 
                        else if(strcmp(neto->filhos[0]->valor,"stroke")==0){
                            //codigo do stroke
                            strokeFlag = 1;
                            stroke(neto);
                        }
                        else if(strcmp(neto->filhos[0]->valor,"noStroke")==0){
                            strokeFlag = 0;
                        }
                        else if(strcmp(neto->filhos[0]->valor,"ellipse")==0){
                            //codigo do ellipse
                            ellipse(neto);
                        }
                        else if(strcmp(neto->filhos[0]->valor,"rect")==0){
                            //codigo do quadrado
                            rect(neto);
                        }
                        else if(strcmp(neto->filhos[0]->valor,"triangle")==0){
                            //codigo do triangle
                            triangle(neto);
                        } 
                        else if(strcmp(neto->filhos[0]->valor,"strokeWeight")==0){
                            //codigo do triangle
                            defaultLineWidth = checkVar(neto->filhos[1]);
                        }
                    }
                    glutSwapBuffers();
                }
            }
        }
        //glClearColor(0.0f, 0.0f, 0.0f, 1.0f); // Set background color to black and opaque
        //glClear(GL_COLOR_BUFFER_BIT);         // Clear the color buffer

        // Draw a Red 1x1 Square centered at origin
    }

    struct no *rootDraw = root;
    for(int i=0; i<rootDraw->num_filhos;i++){
        struct no *filhoDraw = rootDraw->filhos[i];
        if(strcmp(filhoDraw->filhos[0]->valor,"draw")==0){
            //printf("Dentro do draw -> %d\n", filhoDraw->num_filhos);
            //tenho de meter tudo ca dentro agora?
            struct no *netoDraw;
            struct no *linhaAux;
            switchDraw=filhoDraw->num_filhos;
            if(z<filhoDraw->num_filhos){
                //printf("flag %d\n", firstFlag);
                netoDraw = filhoDraw->filhos[z];
                linhaAux=filhoDraw->filhos[z];
                
                /*else{
                    linhaAux=filhoDraw->filhos[z];
                }*/
                printf("teste %s\n", netoDraw->tipo);
                printf("teste %s\n", netoDraw->filhos[0]->valor);
                if(strcmp(netoDraw->tipo,"MethodDecl")==0){
                    if(strcmp(netoDraw->filhos[0]->valor,"background")==0){
                        printf("linha do background n-%d\n",netoDraw->filhos[0]->linha);
                        strcpy(highlightType,"background");
                        replyZ = linhaAux->filhos[0]->linha;
                        //codigo do background
                        background(netoDraw);
                    }
                    else if(strcmp(netoDraw->filhos[0]->valor,"fill")==0){
                        strcpy(highlightType,"fill");
                        replyZ = linhaAux->filhos[0]->linha;
                        //codigo do fill
                        fill(netoDraw);
                    } 
                    else if(strcmp(netoDraw->filhos[0]->valor,"stroke")==0){
                        strcpy(highlightType,"stroke");
                        replyZ = linhaAux->filhos[0]->linha;
                        strokeFlag = 1;
                        //codigo do stroke
                        stroke(netoDraw);
                    }
                    else if(strcmp(netoDraw->filhos[0]->valor,"noStroke")==0){
                        strcpy(highlightType,"noStroke");
                        replyZ = linhaAux->filhos[0]->linha;
                        strokeFlag = 0;
                    }
                    else if(strcmp(netoDraw->filhos[0]->valor,"ellipse")==0){
                        strcpy(highlightType,"ellipse");
                        replyZ = linhaAux->filhos[0]->linha;
                        //codigo do ellipse
                        ellipse(netoDraw);
                    }
                    else if(strcmp(netoDraw->filhos[0]->valor,"rect")==0){
                        strcpy(highlightType,"rect");
                        replyZ = linhaAux->filhos[0]->linha;
                        //codigo do quadrado
                        rect(netoDraw);
                    }
                    else if(strcmp(netoDraw->filhos[0]->valor,"triangle")==0){
                        strcpy(highlightType,"triangle");
                        replyZ = linhaAux->filhos[0]->linha;
                        //codigo do triangle
                        triangle(netoDraw);
                    }
                    else if(strcmp(netoDraw->filhos[0]->valor,"strokeWeight")==0){
                        strcpy(highlightType,"strokeWeight");
                        replyZ = linhaAux->filhos[0]->linha;
                        //codigo do triangle
                        defaultLineWidth = checkVar(netoDraw->filhos[1]);
                        char c[100];
                        sprintf(c,"%d", defaultLineWidth);
                        strcpy(highlightChangeOne,c);
                    }
                }    
                else if(strcmp(netoDraw->tipo,"If")==0){
                    strcpy(highlightType,"If");
                    printf("-----dentro do if--------\n");
                    flagIf = 1;
                    replyZ = linhaAux->filhos[0]->linha;    
                    ifElse(netoDraw);
                    printf("--------saiu do if-------\n");
                }else if(strcmp(netoDraw->tipo,"VarDecl")==0){
                    strcpy(highlightType,"VarDecl");
                    flagVar = 1;
                    replyZ = linhaAux->linha;
                    printf("vardecl linha %d\n",replyZ);
                    //printf("entrei \n");
                    varDeclFunc(netoDraw);

                }else if(strcmp(netoDraw->tipo,"ForInt")==0){
                    flagFor = 1;
                    replyZ = linhaAux->linha;
                    printf("for linha %d\n", replyZ);
                    strcpy(highlightType,"For");
                    varIntForFunc(netoDraw);
                    printf("flag do for %d\n", flagFor);
                }
                glutSwapBuffers();
                //glutPostRedisplay();
            }else if(z==filhoDraw->num_filhos){
                printf("last line.........\n");
                flagLast = 1;
                flagForward=1;
                firstIf = 0;
                flagFirstFor = 0;
                flagVar =0;
                z=0;
            }
        }
    }
    glViewport(wightSize,0,wightSize,hightSize);
    display2();
    /*glViewport(wightSize,0,wightSize,hightSize);
    glMatrixMode(GL_PROJECTION);
	glLoadIdentity();
    gluOrtho2D(0,wightSize,hightSize,0);

    display2();
    glutSwapBuffers();*/
   //glFlush();  // Render now
    
    glViewport(3*wightSize/2,0,3*wightSize/2,hightSize);
    display3();


}

void display2(){
    char *stringVar[varCount+1];
    char destAux[100];
    int auxY,auxX;
    //printf("varCount = %d \n", varCount);
    
    /*while(first!=NULL){
       printf("First id %s\n", first->id);
       printf("First valor %s\n", first->valor);
       first = first->next;
    }*/
    struct varInt *stringAux = first;
    //glClearColor(0.0f, 0.0f, 0.0f, 1.0f); // Set background color to black and opaque
    //glClear(GL_COLOR_BUFFER_BIT);         // Clear the color buffer
    glColor3f(0.0f, 0.0f, 0.0f); // Red 
    glBegin(GL_QUADS);              // Each set of 4 vertices form a quad
        //pontos contra relogio
        glVertex2f(0,0);   // canto superior esquerdo
        glVertex2f(wightSize,0); // canto superior direito
        glVertex2f(wightSize,hightSize); 
        glVertex2f(0,hightSize);
    glEnd();
    for(int i=0;i<=varCount;i++){
        glColor3f (1.0, 1.0, 0.0);
        if(i==0){
            glRasterPos2f(0, 10); //define position on the screen
            stringVar[i] = "System's variables:";
            while(*stringVar[i]){
                glutBitmapCharacter(GLUT_BITMAP_8_BY_13, *stringVar[i]++);
            }
        }
        if(i<3){
            glRasterPos2f(0, 10+((i+1)*10)); //define position on the screen
            auxY = 50+(i+1)*10;
        }else if(i==3){
            glRasterPos2f(0, 40+((i+1)*10)); //define position on the screen
            stringVar[i] = "Defined variables:";
            while(*stringVar[i]){
                glutBitmapCharacter(GLUT_BITMAP_8_BY_13, *stringVar[i]++);
            }
            glRasterPos2f(0, 50+((i+1)*10)); //define position on the screen
            auxY = 50+(i+1)*10;
        }else{
            glRasterPos2f(0, 50+((i+1)*10)); //define position on the screen
            auxY = 50+(i+1)*10;
        }
        if(i==0){
            stringVar[i] = "fill : ";
            while(*stringVar[i]){
                glutBitmapCharacter(GLUT_BITMAP_8_BY_13, *stringVar[i]++);
            }
            glColor3f(fillRed/255, fillGreen/255, fillBlue/255);
            glBegin(GL_QUADS);              // Each set of 4 vertices form a quad
            //pontos contra relogio
                glVertex2f(100,20);   // canto superior esquerdo
                glVertex2f(120,20); // canto superior direito
                glVertex2f(120,11); 
                glVertex2f(100,11);
            glEnd();
            glColor3f(1.0f, 1.0f, 1.0f);
            glLineWidth(1.0f);

            glBegin(GL_LINES);              // Each set of 4 vertices form a quad
                //pontos contra relogio
                glVertex2f(100,20);   // canto superior esquerdo
                glVertex2f(120,20); // canto superior direito
                glVertex2f(120,20); // canto superior direito
                glVertex2f(120,11); 
                glVertex2f(120,11); 
                glVertex2f(100,11);
                glVertex2f(100,11);
                glVertex2f(100,20);   // canto superior esquerdo
            glEnd();
        }else if(i==1){
            if(strokeFlag==1){
                glColor3f(strokeRed/255, strokeGreen/255, strokeBlue/255);
                glBegin(GL_QUADS);              // Each set of 4 vertices form a quad
                    //pontos contra relogio
                    glVertex2f(190,30);   // canto superior esquerdo
                    glVertex2f(210,30); // canto superior direito
                    glVertex2f(210,20); 
                    glVertex2f(190,20);
                glEnd();
                glColor3f(1.0f, 1.0f, 1.0f);
                glLineWidth(1.0f);

                glBegin(GL_LINES);              // Each set of 4 vertices form a quad
                    //pontos contra relogio
                    glVertex2f(190,30);   // canto superior esquerdo
                    glVertex2f(210,30); // canto superior direito
                    glVertex2f(210,30); // canto superior direito
                    glVertex2f(210,20); 
                    glVertex2f(210,20); 
                    glVertex2f(190,20);
                    glVertex2f(190,20);
                    glVertex2f(190,30);   // canto superior esquerdo
                glEnd();
                strcpy(destAux, "stroke : On");
            }
            else{
                strcpy(destAux, "stroke : Off");
            }
            stringVar[i] = destAux;
            while(*stringVar[i]){
                glutBitmapCharacter(GLUT_BITMAP_8_BY_13, *stringVar[i]++);
            }
        }else if(i==2){
            char c[100];
            strcpy(destAux,"strokeWeight : ");
            sprintf(c,"%d", defaultLineWidth);
            strcat(destAux, c);
            stringVar[i] = destAux;
            while(*stringVar[i]){
                glutBitmapCharacter(GLUT_BITMAP_8_BY_13, *stringVar[i]++);
            }
        }else{
            //printf("id = %s\n",stringAux->id);
            //printf("i = %d\n",i);
            if(strcmp(stringAux->tipoVariavel,"Color")==0){
                int yy = 0;
                strcpy(destAux, "color");
                strcat(destAux, " ");
                strcat(destAux, stringAux->id);
                strcat(destAux, " = ");
                auxX = strlen(destAux)*15;
                //printf("auxiliar %s\n",stringAux->valor);
                char *auxChar = (char*) malloc(sizeof(char)*strlen(stringAux->valor)+1);
                strcpy(auxChar,stringAux->valor);
                //printf("auxiliar %s\n",auxChar);
                char *token = strtok(auxChar,",");
                char *array[3];
                while(token!=NULL){
                    array[yy++] = token;
                    token = strtok(NULL, ",");
                }
                float colorAuxRed = atof(array[0])/255;
                //printf("token %f\n",colorAux);
                float colorAuxGreen = atof(array[1])/255;
                //printf("token %f\n",colorAux);
                float colorAuxBlue = atof(array[2])/255;
                //printf("token %f\n",colorAux);
                //printf("X = %d\n", auxX);
                //printf("Y = %d\n", auxY);
                glColor3f(colorAuxRed,colorAuxGreen,colorAuxBlue);
                glBegin(GL_QUADS);              // Each set of 4 vertices form a quad
                //pontos contra relogio
                    glVertex2f(auxX,auxY-9);   // canto superior esquerdo
                    glVertex2f(auxX+20,auxY-9); // canto superior direito
                    glVertex2f(auxX+20,auxY); 
                    glVertex2f(auxX,auxY);
                glEnd();
                glColor3f(1.0f, 1.0f, 1.0f);
                glLineWidth(1.0f);

                glBegin(GL_LINES);              // Each set of 4 vertices form a quad
                    //pontos contra relogio
                    glVertex2f(auxX,auxY-9);   // canto superior esquerdo
                    glVertex2f(auxX+20,auxY-9); // canto superior direito
                    glVertex2f(auxX+20,auxY-9); // canto superior direito
                    glVertex2f(auxX+20,auxY); 
                    glVertex2f(auxX+20,auxY); 
                    glVertex2f(auxX,auxY);
                    glVertex2f(auxX,auxY);
                    glVertex2f(auxX,auxY-9);   // canto superior esquerdo
                glEnd();
            }else if(strcmp(stringAux->tipoVariavel,"Int")==0){
                strcpy(destAux, "int");
                strcat(destAux, " ");
                strcat(destAux, stringAux->id);
                strcat(destAux, " = ");
                strcat(destAux, stringAux->valor);
            }else{
                strcpy(destAux, "float");
                strcat(destAux, " ");
                strcat(destAux, stringAux->id);
                strcat(destAux, " = ");
                strcat(destAux, stringAux->valor);
            }
            stringVar[i] = destAux;
            stringAux = stringAux->next;
            while(*stringVar[i]){
                glutBitmapCharacter(GLUT_BITMAP_8_BY_13, *stringVar[i]++);
            }
        }
    }
    glBegin(GL_QUADS);              // Each set of 4 vertices form a quad
        //pontos contra relogio
        glVertex2f(wightSize/2,hightSize-10);   // canto superior esquerdo
        glVertex2f(3*wightSize/4,hightSize-10); // canto superior direito
        glVertex2f(3*wightSize/4,hightSize-50); 
        glVertex2f(wightSize/2,hightSize-50);
    glEnd();
    
    //highlight here
    highlightAux();

    //botão next
    glColor3f (1.0, 0.0, 0.0);
    glRasterPos2f(11*wightSize/20, hightSize-25);
    strcpy(destAux, "NEXT");
    stringVar[0] = destAux;
    while(*stringVar[0]){
        glutBitmapCharacter(GLUT_BITMAP_8_BY_13, *stringVar[0]++);
    }
    glutSwapBuffers();
}

void display3(){
    FILE *fptr;
    int bufferLen=128;
    char cc[bufferLen];
    char auxCC[100];
    int pos=0;
    int posX=1;

    glColor3f(0.0f, 0.0f, 0.0f); 
    glBegin(GL_QUADS);              // Each set of 4 vertices form a quad
        //pontos contra relogio
        glVertex2f(0,0);   // canto superior esquerdo
        glVertex2f(3*wightSize/2,0); // canto superior direito
        glVertex2f(3*wightSize/2,hightSize); 
        glVertex2f(0,hightSize);
    glEnd();
    glColor3f (1.0, 1.0, 0.0);
    // Open file
    fptr = fopen("test2.txt", "r");
    if (fptr == NULL)
    {
        printf("Cannot open file \n");
        exit(0);
    }
  
    while(fgets(cc,bufferLen,fptr)!=NULL){
        glRasterPos2f(0, 10+(pos*15));
        int i=0;
        while(cc[i]!=NULL){
            if (cc[i]=='\n')
            {
                //printf("linha\n");
            }else{
                glutBitmapCharacter(GLUT_BITMAP_8_BY_13, cc[i]);}
                i++;
            }
        //printf("setup lines %d\n", setupAux);
        pos++;
    }
  
    fclose(fptr);
    glColor3f(1.0f, 0.0f, 0.0f);
    //replyZ=pos-switchDraw;
    /*if(z==switchDraw-1){
        printf("aint going in\n");
    }else{*/
    if(flagFirst==0){
        printf("primeira linha numero: %d\n",replyZ-1);
        printf("flag %d\n",flagFirst);
        lastReplyZ = replyZ-1;
        glBegin(GL_LINE_LOOP);              // Each set of 4 vertices form a quad
            //pontos contra relogio
            glVertex2f(1,1+((replyZ-1)*15));   // canto superior esquerdo
            glVertex2f(330,1+((replyZ-1)*15)); // canto superior direito
            //glVertex2f(330,1+((replyZ-1)*15)); 
            glVertex2f(330,12+((replyZ-1)*15));
            //glVertex2f(330,12+((replyZ-1)*15));   // canto superior esquerdo
            glVertex2f(1,12+((replyZ-1)*15)); // canto superior direito
            //glVertex2f(1,12+((replyZ-1)*15)); 
            //glVertex2f(1,1+((replyZ-1)*15));
        glEnd();
        flagFirst=1;
    }else if(flagLast==1){
        printf("ultima linha numero: %d\n",lastReplyZ);
        glBegin(GL_LINE_LOOP);              // Each set of 4 vertices form a quad
        //pontos contra relogio
        glVertex2f(1,1+((lastReplyZ)*15));   // canto superior esquerdo
        glVertex2f(330,1+((lastReplyZ)*15)); // canto superior direito
        //glVertex2f(330,1+((replyZ-1)*15)); 
        glVertex2f(330,12+((lastReplyZ)*15));
        //glVertex2f(330,12+((replyZ-1)*15));   // canto superior esquerdo
        glVertex2f(1,12+((lastReplyZ)*15)); // canto superior direito
        //glVertex2f(1,12+((replyZ-1)*15)); 
        //glVertex2f(1,1+((replyZ-1)*15));
        glEnd();
        flagLast=0;
    }else{
        printf("linha numero: %d\n",replyZ);
        glBegin(GL_LINE_LOOP);              // Each set of 4 vertices form a quad
            //pontos contra relogio
            glVertex2f(1,1+((replyZ)*15));   // canto superior esquerdo
            glVertex2f(330,1+((replyZ)*15)); // canto superior direito
            //glVertex2f(330,1+((replyZ-1)*15)); 
            glVertex2f(330,12+((replyZ)*15));
            //glVertex2f(330,12+((replyZ-1)*15));   // canto superior esquerdo
            glVertex2f(1,12+((replyZ)*15)); // canto superior direito
            //glVertex2f(1,12+((replyZ-1)*15)); 
            //glVertex2f(1,1+((replyZ-1)*15));
        glEnd();
    }
}

void background (struct no* neto){
    float red, blue, green;
    if(strcmp(neto->filhos[1]->tipo,"Virgula")==0){
        red = checkVar(neto->filhos[1]->filhos[0]->filhos[0])/255;
        green = checkVar(neto->filhos[1]->filhos[0]->filhos[1])/255;
        blue = checkVar(neto->filhos[1]->filhos[1])/255;
        //printf("3 argumentos \n");
    }
    else {
        //quando so tem um arguemento tipo 255
        red = checkVar(neto->filhos[1])/255.0;
        green = checkVar(neto->filhos[1])/255.0;
        blue = checkVar(neto->filhos[1])/255.0;
    }
    highlightChangeFloat[0]=red;
    highlightChangeFloat[1]=green;
    highlightChangeFloat[2]=blue;
    //printf("no background \n");
    glColor3f(red,green,blue); // Red 
    glBegin(GL_QUADS);              // Each set of 4 vertices form a quad
        //pontos contra relogio
        glVertex2f(0,0);   // canto superior esquerdo
        glVertex2f(wightSize,0); // canto superior direito
        glVertex2f(wightSize,hightSize); 
        glVertex2f(0,hightSize);
    glEnd();
    //glClearColor(red, blue, green, 1.0f); // Set background color and opaque
    //glClear(GL_COLOR_BUFFER_BIT);         // Clear the color buffer
}

void fill(struct no* neto){
    if(strcmp(neto->filhos[1]->tipo,"Virgula")==0){
        fillRed = checkVar(neto->filhos[1]->filhos[0]->filhos[0]);
        fillGreen = checkVar(neto->filhos[1]->filhos[0]->filhos[1]);
        fillBlue = checkVar(neto->filhos[1]->filhos[1]);
        printf("3 argumentos fill\n");
    }
    else {
        printf("fill tipo here -> %s\n",neto->filhos[1]->tipo);
        if(strcmp(neto->filhos[1]->tipo,"Id")==0){
            struct varInt *new = first;
            //printf("no id\n");
            while(new!=NULL){
                printf("no while no fill -> %s\n", new->id);
                if(strcmp(neto->filhos[1]->valor,new->id)==0){
                    if(strcmp(new->tipoVariavel,"Color")==0){
                        printf("inside color fill\n");
                        int yy=0;
                        char *auxChar = (char*) malloc(sizeof(char)*strlen(new->valor)+1);
                        strcpy(auxChar,new->valor);
                        char *token = strtok(auxChar,",");
                        char *array[3];
                        while(token!=NULL){
                            array[yy++] = token;
                            token = strtok(NULL, ",");
                        }
                        fillRed = atof(array[0]);
                        printf("token %f\n",fillRed);
                        fillGreen = atof(array[1]);
                        printf("token %f\n",fillGreen);
                        fillBlue = atof(array[2]);
                        printf("token %f\n",fillBlue);
                    }else{
                        fillRed = checkVar(neto->filhos[1]);
                        fillGreen = checkVar(neto->filhos[1]);
                        fillBlue = checkVar(neto->filhos[1]);
                    }
                }
                new = new->next;
            }
        }else{
            //quando so tem um arguemento tipo 255
            fillRed = checkVar(neto->filhos[1]);
            fillGreen = checkVar(neto->filhos[1]);
            fillBlue = checkVar(neto->filhos[1]);
            printf("1 argumento fill -> %f\n", fillRed);
        }
    }

    highlightChangeFloat[0]=fillRed;
    highlightChangeFloat[1]=fillGreen;
    highlightChangeFloat[2]=fillBlue;

    //teste
    glBegin(GL_QUADS);              
        glVertex2f(10000,10000);   // canto superior esquerdo
        glVertex2f(10000,10000); // canto superior direito
        glVertex2f(10000,10000); 
        glVertex2f(10000,10000);
    glEnd();
}

void rect(struct no* neto){
    int x,y,largura,altura; 
    struct no *auxRect = neto->filhos[1];
    x = checkVar(auxRect->filhos[0]->filhos[0]->filhos[0]);
    y = checkVar(auxRect->filhos[0]->filhos[0]->filhos[1]);
    largura = checkVar(auxRect->filhos[0]->filhos[1]);
    altura = checkVar(auxRect->filhos[1]);
    glColor3f(fillRed/255, fillGreen/255, fillBlue/255); // Red 
    
    char c[100];
    sprintf(c, "%d", x);
    strcpy(highlightChangeOne,c); //x do canto superior direito

    sprintf(c, "%d", y);
    strcpy(highlightChangeTwo,c); //y do canto superior direito
    
    sprintf(c, "%d", largura);
    strcpy(highlightChangeThree,c); //largura do rectangulo
    
    sprintf(c, "%d", altura);
    strcpy(highlightChangeFour,c); //altura do rectangulo

    glBegin(GL_QUADS);              
        glVertex2f(x,y);   // canto superior esquerdo
        glVertex2f(x+largura,y); // canto superior direito
        glVertex2f(x+largura,y+altura); 
        glVertex2f(x,y+altura);
    glEnd();
    //glEnd();

    if(strokeFlag == 1){
        //printf("im innnnnnnnnnnnnnnnnnnnnn\n");
        glColor3f(strokeRed/255, strokeGreen/255, strokeBlue/255);
        glLineWidth(defaultLineWidth);

        glBegin(GL_LINES);              // Each set of 4 vertices form a quad
            //pontos contra relogio
            glVertex2f(x,y);   // canto superior esquerdo
            glVertex2f(x+largura,y); // canto superior direito
            glVertex2f(x+largura,y); // canto superior direito
            glVertex2f(x+largura,y+altura); 
            glVertex2f(x+largura,y+altura); 
            glVertex2f(x,y+altura);
            glVertex2f(x,y+altura);
            glVertex2f(x,y);   // canto superior esquerdo
        glEnd();
    }
}

void ellipse(struct no* neto){ 
    //printf("dentro da ellipse\n");
    int xp, yp, widthR, heightR;

    xp = checkVar(neto->filhos[1]->filhos[0]->filhos[0]->filhos[0]);
    yp = checkVar(neto->filhos[1]->filhos[0]->filhos[0]->filhos[1]);
    widthR = checkVar(neto->filhos[1]->filhos[0]->filhos[1]);
    heightR = checkVar(neto->filhos[1]->filhos[1]);
    

    char c[100];
    sprintf(c, "%d", xp);
    strcpy(highlightChangeOne,c); //x do centro da ellipse

    sprintf(c, "%d", yp);
    strcpy(highlightChangeTwo,c); //y do centro da ellipse

    sprintf(c, "%d", widthR);
    strcpy(highlightChangeThree,c); //diametro na horizontal

    sprintf(c, "%d", heightR);
    strcpy(highlightChangeFour,c); //diametro na vertical
    

    //printf("fillColor on elipse: red %f green %f blue %f\n", fillRed,fillGreen,fillGreen);
    //glClearColor(250.0f,250.0f,250.0f,1.0f);
    glColor3f(fillRed/255,fillGreen/255,fillBlue/255);
    glLineWidth(defaultLineWidth);
    

    glBegin(GL_TRIANGLE_FAN);
        glVertex2d(xp, yp);
        for(int i = 0; i <= 180; i++){
            glVertex2f((xp + (widthR*cos(i*(2*3.14)/180))),(yp + (heightR*sin(i*(2*3.14)/180))));
        }
    glEnd();

    if(strokeFlag == 1){
        glPointSize(defaultLineWidth);
        glColor3f(strokeRed/255,strokeGreen/255,strokeBlue/255);
        glBegin(GL_POINTS);
        //tem de ter estes pontos para ficar melhor definido
        for(int i = 0; i <= 1440; i++){
            glVertex2f((xp + (widthR*cos(i*(2*3.14)/1440))),(yp + (heightR*sin(i*(2*3.14)/1440))));
        }
        glEnd();
    }
}

void stroke(struct no* neto){
    if(strcmp(neto->filhos[1]->tipo,"Virgula")==0){
        strokeRed = checkVar(neto->filhos[1]->filhos[0]->filhos[0]);
        strokeGreen = checkVar(neto->filhos[1]->filhos[0]->filhos[1]);
        strokeBlue = checkVar(neto->filhos[1]->filhos[1]);
        //printf("3 argumentos stroke\n");
    }
    else {
        //quando so tem um arguemento tipo 255
        strokeRed = checkVar(neto->filhos[1]);
        strokeGreen = checkVar(neto->filhos[1]);
        strokeBlue = checkVar(neto->filhos[1]);
        //printf("1 argumento stroke\n");
    }
}

void myMouseHandler(int button, int state, int x, int y){
    if(button==GLUT_RIGHT_BUTTON && state==GLUT_DOWN){
        if(flagIf==0 && flagVar==0 && flagFor==0){
            if(z<switchDraw){
                if(x>(wightSize+(wightSize/4)) && x<(wightSize+(3*wightSize/8)) && y>(hightSize-50) && y<(hightSize-10)){
                    z++;
                }
            }else{
                z=0;
            }
        }else if(flagForForIf==1){
            if(u<forAux){
                if(x>(wightSize+(wightSize/4)) && x<(wightSize+(3*wightSize/8)) && y>(hightSize-50) && y<(hightSize-10)){
                    u++;
                }
            }else{
                u=0;
            }
        }else if(flagIf==1 && flagForForIf==0){
            if(t<ifAux){
                if(x>(wightSize+(wightSize/4)) && x<(wightSize+(3*wightSize/8)) && y>(hightSize-50) && y<(hightSize-10)){
                    t++;
                }
            }else{
                t=0;
            }
        }else if(flagVar==1){
            if(f<1){
                if(x>(wightSize+(wightSize/4)) && x<(wightSize+(3*wightSize/8)) && y>(hightSize-50) && y<(hightSize-10)){
                    f++;
                    z++;
                }
            }else{
                f=0;
                //flagVar=0;
            }
        }else if(flagFor==1){
            if(u<forAux){
                if(x>(wightSize+(wightSize/4)) && x<(wightSize+(3*wightSize/8)) && y>(hightSize-50) && y<(hightSize-10)){
                    u++;
                }
            }else{
                u=0;
            }
        }
        
        glutSwapBuffers();
    }
    printf("z->%d\n",z);
    printf("t->%d\n",t);
    printf("f->%d\n",f);
    printf("u->%d\n",u);
    printf("----------------\n");
    printf("flagIF->%d\n",flagIf);
    printf("flagVar->%d\n",flagVar);
    printf("flagFor->%d\n",flagFor);
}

void triangle(struct no* neto){
    //printf("trinaglo\n");
    int primX, primY, segX, segY, tercX, tercY;
    struct no* auxNeto = neto->filhos[1];
    primX = checkVar(auxNeto->filhos[0]->filhos[0]->filhos[0]->filhos[0]->filhos[0]);
    primY = checkVar(auxNeto->filhos[0]->filhos[0]->filhos[0]->filhos[0]->filhos[1]);
    segX = checkVar(auxNeto->filhos[0]->filhos[0]->filhos[0]->filhos[1]);    
    segY = checkVar(auxNeto->filhos[0]->filhos[0]->filhos[1]);
    tercX = checkVar(auxNeto->filhos[0]->filhos[1]);
    tercY = checkVar(auxNeto->filhos[1]);

    char c[100];
    sprintf(c, "%d", primX);
    strcpy(highlightChangeOne,c); //x do primeiro canto

    sprintf(c, "%d", primY);
    strcpy(highlightChangeTwo,c); //y do primeiro canto
    
    sprintf(c, "%d", segX);
    strcpy(highlightChangeThree,c); //x do segundo canto
    
    sprintf(c, "%d", segY);
    strcpy(highlightChangeFour,c); //y do segundo canto

    sprintf(c, "%d", tercX);
    strcpy(highlightChangeFive,c); //x do terceiro canto
    
    sprintf(c, "%d", tercY);
    strcpy(highlightChangeSix,c); //y do terceiro canto

    glColor3f(fillRed/255, fillGreen/255, fillBlue/255); // Red
    glBegin(GL_TRIANGLES);
        glVertex2f( primX, primY );
        glVertex2f( segX, segY );
        glVertex2f( tercX, tercY );
    glEnd(); 
    
    if(strokeFlag == 1){
        glColor3f(strokeRed/255, strokeGreen/255, strokeBlue/255);
        glLineWidth(defaultLineWidth);

        glBegin(GL_LINES);              // Each set of 4 vertices form a quad
            //pontos contra relogio
            glVertex2f( primX, primY );   // canto superior esquerdo
            glVertex2f( segX, segY );
            glVertex2f( segX, segY );
            glVertex2f( tercX, tercY );  
            glVertex2f( tercX, tercY );
            glVertex2f( primX, primY );
        glEnd();
    }
}

float checkVar(struct no *varAux){
    //printf("isto funciona\n");
    //printf("varaux = %s\n", varAux->tipo);
    int expA,expB;
    if(strcmp(varAux->tipo, "Id")==0){
        struct varInt *temp = first;
        //printf("no id\n");
        while(temp!=NULL){
            //printf("no while -> %s\n", temp->id);
            if(strcmp(varAux->valor,temp->id)==0){
                //printf("id %s\n", temp->id);
                //printf("valor %s\n", temp->valor);
                return(atof(temp->valor));
            }
            temp = temp->next;
        }
    }else if(strcmp(varAux->tipo, "Div")==0){
        //printf("div\n");
        strcpy(highlightChangeSix,"/");
        expA = checkVar(varAux->filhos[0]);
        expB = checkVar(varAux->filhos[1]);
        return(expA/expB);
    }else if(strcmp(varAux->tipo, "Multi")==0){
        strcpy(highlightChangeSix,"*");
        //printf("multi\n");
        expA = checkVar(varAux->filhos[0]);
        expB = checkVar(varAux->filhos[1]);
        return(expA*expB);
    }else if(strcmp(varAux->tipo, "Soma")==0){
        strcpy(highlightChangeSix,"+");
        //printf("soma\n");
        expA = checkVar(varAux->filhos[0]);
        expB = checkVar(varAux->filhos[1]);
        return(expA+expB);
    }else if(strcmp(varAux->tipo, "Subt")==0){
        strcpy(highlightChangeSix,"-");
        //printf("subt\n");
        expA = checkVar(varAux->filhos[0]);
        expB = checkVar(varAux->filhos[1]);
        return(expA-expB);
    }else if(strcmp(varAux->tipo, "Mod")==0){
        strcpy(highlightChangeSix,"%");
        //printf("subt\n");
        expA = checkVar(varAux->filhos[0]);
        expB = checkVar(varAux->filhos[1]);
        return(expA%expB);
    }else{
        //printf("var int\n");
        return(atof(varAux->valor));
    }
    return;
}

void ifElse(struct no* neto){
    ifTrue = ifValue(neto->filhos[0]); //resolver o valor do if
    if(firstIf==0){
        printf("first if\n");
        firstIf = 1;
        t=-1;
    }else{
        if(ifTrue){ //se a condição for verdadeira
            struct no* netoIf;
            struct no* netoAux;
            if(strcmp(neto->filhos[1]->tipo,"Bloco")==0){
                printf("é bloco\n");
                ifAux = neto->filhos[1]->num_filhos;
                netoAux=neto->filhos[1];
            }else{
                ifAux = neto->num_filhos;
                netoAux=neto;
            }    
            if(t<netoAux->num_filhos){
                netoIf = netoAux->filhos[t];
                //printf("tipo do no do if %s\n", netoIf->tipo);
                printf("tipo do no neto do if %s\n", netoIf->filhos[0]->valor);
                if(strcmp(netoIf->tipo,"MethodDecl")==0){
                    if(strcmp(netoIf->filhos[0]->valor,"background")==0){
                        strcpy(highlightType,"background");
                        replyZ = netoIf->filhos[0]->linha;
                        //codigo do background
                        background(netoIf);
                    }
                    else if(strcmp(netoIf->filhos[0]->valor,"fill")==0){
                        strcpy(highlightType,"fill");
                        replyZ = netoIf->filhos[0]->linha;
                        //codigo do fill
                        fill(netoIf);
                    } 
                    else if(strcmp(netoIf->filhos[0]->valor,"stroke")==0){
                        strcpy(highlightType,"stroke");
                        replyZ = netoIf->filhos[0]->linha;
                        strokeFlag = 1;
                        //codigo do stroke
                        stroke(netoIf);
                    }
                    else if(strcmp(netoIf->filhos[0]->valor,"noStroke")==0){
                        strcpy(highlightType,"noStroke");
                        replyZ = netoIf->filhos[0]->linha;
                        strokeFlag = 0;
                    }
                    else if(strcmp(netoIf->filhos[0]->valor,"ellipse")==0){
                        strcpy(highlightType,"ellipse");
                        replyZ = netoIf->filhos[0]->linha;
                        //codigo do ellipse
                        ellipse(netoIf);
                    }
                    else if(strcmp(netoIf->filhos[0]->valor,"rect")==0){
                        strcpy(highlightType,"rect");
                        replyZ = netoIf->filhos[0]->linha;
                        //codigo do quadrado
                        rect(netoIf);
                    }
                    else if(strcmp(netoIf->filhos[0]->valor,"triangle")==0){
                        strcpy(highlightType,"triangle");
                        replyZ = netoIf->filhos[0]->linha;
                        printf("linha do triangulo do if n-%d\n",netoIf->filhos[0]->linha);
                        //codigo do triangle
                        triangle(netoIf);
                    }
                    else if(strcmp(netoIf->filhos[0]->valor,"strokeWeight")==0){
                        strcpy(highlightType,"strokeWeight");
                        replyZ = netoIf->filhos[0]->linha;
                        //codigo do triangle
                        defaultLineWidth = checkVar(netoIf->filhos[1]);
                        char c[100];
                        sprintf(c,"%d", defaultLineWidth);
                        strcpy(highlightChangeOne,c);
                    }
                }else if(strcmp(netoIf->tipo,"ForInt")==0){
                    flagForForIf = 1;
                    replyZ = netoIf->linha;
                    printf("for linha %d\n", replyZ);
                    strcpy(highlightType,"For");
                    varIntForFunc(netoIf);
                    printf("flag do for no if %d\n", flagForForIf);
                    flagForForIf = 0;
                    printf("flag do for no if %d\n", flagForForIf);
                }
                glutSwapBuffers();
                /*else if(strcmp(netoIf->tipo,"If")==0){
                    flagIf = 1;
                    ifElse(netoIf);
                    flagIf = 0;
                }*/
            }else if(t==netoAux->num_filhos){
                t=0;
                //z++;
                flagIf=0;
            }
        }else if(neto->filhos[2]->num_filhos>0){ //se a condição for falsa e existir um else
            printf("else? %s\n", neto->filhos[2]->tipo);
            printf("o else resulta\n");
            ifAux = neto->filhos[2]->num_filhos;
            struct no* netoIf;
            struct no* netoAux=neto->filhos[2];
            if(t<netoAux->num_filhos){
                netoIf = netoAux->filhos[t];
                printf("tipo do no do if %s\n", netoIf->tipo);
                printf("tipo do no neto do if %s\n", netoIf->filhos[0]->valor);
                if(strcmp(netoIf->tipo,"MethodDecl")==0){
                    if(strcmp(netoIf->filhos[0]->valor,"background")==0){
                        strcpy(highlightType,"background");
                        replyZ = netoIf->filhos[0]->linha;
                        //codigo do background
                        background(netoIf);
                    }
                    else if(strcmp(netoIf->filhos[0]->valor,"fill")==0){
                        strcpy(highlightType,"fill");
                        replyZ = netoIf->filhos[0]->linha;
                        //codigo do fill
                        fill(netoIf);
                    } 
                    else if(strcmp(netoIf->filhos[0]->valor,"stroke")==0){
                        strcpy(highlightType,"stroke");
                        replyZ = netoIf->filhos[0]->linha;
                        strokeFlag = 1;
                        //codigo do stroke
                        stroke(netoIf);
                    }
                    else if(strcmp(netoIf->filhos[0]->valor,"noStroke")==0){
                        strcpy(highlightType,"noStroke");
                        replyZ = netoIf->filhos[0]->linha;
                        strokeFlag = 0;
                    }
                    else if(strcmp(netoIf->filhos[0]->valor,"ellipse")==0){
                        strcpy(highlightType,"ellipse");
                        replyZ = netoIf->filhos[0]->linha;
                        //codigo do ellipse
                        ellipse(netoIf);
                    }
                    else if(strcmp(netoIf->filhos[0]->valor,"rect")==0){
                        strcpy(highlightType,"rect");
                        replyZ = netoIf->filhos[0]->linha;
                        //codigo do quadrado
                        rect(netoIf);
                    }
                    else if(strcmp(netoIf->filhos[0]->valor,"triangle")==0){
                        strcpy(highlightType,"triangle");
                        replyZ = netoIf->filhos[0]->linha;
                        //codigo do triangle
                        triangle(netoIf);
                    }
                    else if(strcmp(netoIf->filhos[0]->valor,"strokeWeight")==0){
                        strcpy(highlightType,"strokeWeight");
                        replyZ = netoIf->filhos[0]->linha;
                        //codigo do triangle
                        defaultLineWidth = checkVar(netoIf->filhos[1]);
                        char c[100];
                        sprintf(c,"%d", defaultLineWidth);
                        strcpy(highlightChangeOne,c);
                    }
                }else if(strcmp(netoIf->tipo,"ForInt")==0){
                    flagForForIf = 1;
                    replyZ = netoIf->linha;
                    printf("for linha %d\n", replyZ);
                    strcpy(highlightType,"For");
                    varIntForFunc(netoIf);
                    printf("flag do for no if %d\n", flagForForIf);
                    printf("flag do for no if %d\n", flagForForIf);
                }
                glutSwapBuffers();
                /*else if(strcmp(netoIf->tipo,"If")==0){
                    flagIf = 1;
                    ifElse(netoIf);
                    flagIf = 0;
                }*/
            }else if(t==netoAux->num_filhos){
                t=0;
                //z++;
                flagIf=0;
            }
            //no fim mudar a flag
            //flagIf=0;
        }
    }
}

boolean ifValue(struct no* neto){
    //cada um tem de ter um if que retorna false ou true
    int auxUm, auxDois;
    char c[100];
    char cDois[100];
    printf("ifValue %s\n", neto->tipo);
    if(strcmp(neto->tipo,"And")==0){//and
        flagIfTwoArguments = 1;
        strcpy(highlightChangeOne,"&&");
        if(ifValue(neto->filhos[0]) && ifValue(neto->filhos[1])){
            strcpy(highlightChangeSix,"TRUE");
            return TRUE;
        }else{
            strcpy(highlightChangeSix,"FALSE");
            return FALSE;
        }
    }else if(strcmp(neto->tipo,"Or")==0){//or
        flagIfTwoArguments = 1;
        strcpy(highlightChangeOne,"||");
        if(ifValue(neto->filhos[0]) || ifValue(neto->filhos[1])){
            strcpy(highlightChangeSix,"TRUE");
            return TRUE;
        }else{
            strcpy(highlightChangeSix,"FALSE");
            return FALSE;
        }
    }else if(strcmp(neto->tipo,"Eq")==0){//eq
        printf("entrei no eq\n");
        auxUm = checkVar(neto->filhos[0]);
        char *test;
        test = (char *) malloc(sizeof(char) * (strlen(neto->filhos[0]->valor)+1));
        if(neto->filhos[0]->num_filhos==2){
            strcpy(test, neto->filhos[0]->filhos[0]->valor);
            strcat(test,highlightChangeSix);
            strcat(test, neto->filhos[0]->filhos[1]->valor);
        }else{
            strcpy(test, neto->filhos[0]->valor);
        }
        strcpy(c, test);
        auxDois = checkVar(neto->filhos[1]);
        //sprintf(c,"%f",auxUm);
        sprintf(cDois,"%d",auxDois);
        if(checkVar(neto->filhos[0])==checkVar(neto->filhos[1])){
            if(flagIfTwoArguments==1 && flagUseThree==0){
                strcpy(highlightChangeTwo,c);
                strcat(highlightChangeTwo," == ");
                strcat(highlightChangeTwo,cDois);
                strcpy(highlightChangeFour,"TRUE");
                flagUseThree = 1;
            }else if(flagIfTwoArguments==1 && flagUseThree==1){
                strcpy(highlightChangeThree,c);
                strcat(highlightChangeThree," == ");
                strcat(highlightChangeThree,cDois);
                strcpy(highlightChangeFive,"TRUE");
                flagUseThree = 0;
            }else{
                strcpy(highlightChangeTwo,c);
                strcat(highlightChangeTwo," == ");
                strcat(highlightChangeTwo,cDois);
                strcpy(highlightChangeThree,"TRUE");
            }
            return TRUE;
        }else{
            if(flagIfTwoArguments==1 && flagUseThree==0){
                strcpy(highlightChangeTwo,c);
                strcat(highlightChangeTwo," == ");
                strcat(highlightChangeTwo,cDois);
                strcpy(highlightChangeFour,"FALSE");
                flagUseThree = 1;
            }else if(flagIfTwoArguments==1 && flagUseThree==1){
                strcpy(highlightChangeThree,c);
                strcat(highlightChangeThree," == ");
                strcat(highlightChangeThree,cDois);
                strcpy(highlightChangeFive,"FALSE");
                flagUseThree = 0;
            }else{
                strcpy(highlightChangeTwo,c);
                strcat(highlightChangeTwo," == ");
                strcat(highlightChangeTwo,cDois);
                strcpy(highlightChangeThree,"FALSE");
            }
            return FALSE;
        }
    }else if(strcmp(neto->tipo,"Diferente")==0){//diferente
        char *test;
        test = (char *) malloc(sizeof(char) * (strlen(neto->filhos[0]->valor)+1));
        strcpy(test, neto->filhos[0]->valor);
        strcpy(c, test);
        //auxUm = checkVar(neto->filhos[0]);
        auxDois = checkVar(neto->filhos[1]);
        //sprintf(c,"%f",auxUm);
        sprintf(cDois,"%d",auxDois);
        if(checkVar(neto->filhos[0])!=checkVar(neto->filhos[1])){
            if(flagIfTwoArguments==1 && flagUseThree==0){
                strcpy(highlightChangeTwo,c);
                strcat(highlightChangeTwo," != ");
                strcat(highlightChangeTwo,cDois);
                strcpy(highlightChangeFour,"TRUE");
                flagUseThree = 1;
            }else if(flagIfTwoArguments==1 && flagUseThree==1){
                strcpy(highlightChangeThree,c);
                strcat(highlightChangeThree," != ");
                strcat(highlightChangeThree,cDois);
                strcpy(highlightChangeFive,"TRUE");
                flagUseThree = 0;
            }else{
                strcpy(highlightChangeTwo,c);
                strcat(highlightChangeTwo," != ");
                strcat(highlightChangeTwo,cDois);
                strcpy(highlightChangeThree,"TRUE");
            }
            return TRUE;
        }else{
            if(flagIfTwoArguments==1 && flagUseThree==0){
                strcpy(highlightChangeTwo,c);
                strcat(highlightChangeTwo," != ");
                strcat(highlightChangeTwo,cDois);
                strcpy(highlightChangeFour,"FALSE");
                flagUseThree = 1;
            }else if(flagIfTwoArguments==1 && flagUseThree==1){
                strcpy(highlightChangeThree,c);
                strcat(highlightChangeThree," != ");
                strcat(highlightChangeThree,cDois);
                strcpy(highlightChangeFive,"FALSE");
                printf("three and c %s\n", highlightChangeThree);
                flagUseThree = 0;
            }else{
                strcpy(highlightChangeTwo,c);
                strcat(highlightChangeTwo," != ");
                strcat(highlightChangeTwo,cDois);
                strcpy(highlightChangeThree,"FALSE");
            }
            return FALSE;
        }
    }else if(strcmp(neto->tipo,"Maior")==0){//maior
        char *test;
        test = (char *) malloc(sizeof(char) * (strlen(neto->filhos[0]->valor)+1));
        strcpy(test, neto->filhos[0]->valor);
        strcpy(c, test);
        //auxUm = checkVar(neto->filhos[0]);
        auxDois = checkVar(neto->filhos[1]);
        //sprintf(c,"%f",auxUm);
        sprintf(cDois,"%d",auxDois);
        if(checkVar(neto->filhos[0])>checkVar(neto->filhos[1])){
            if(flagIfTwoArguments==1 && flagUseThree==0){
                strcpy(highlightChangeTwo,c);
                strcat(highlightChangeTwo," > ");
                strcat(highlightChangeTwo,cDois);
                strcpy(highlightChangeFour,"TRUE");
                flagUseThree = 1;
            }else if(flagIfTwoArguments==1 && flagUseThree==1){
                strcpy(highlightChangeThree,c);
                strcat(highlightChangeThree," > ");
                strcat(highlightChangeThree,cDois);
                strcpy(highlightChangeFive,"TRUE");
                flagUseThree = 0;
            }else{
                strcpy(highlightChangeTwo,c);
                strcat(highlightChangeTwo," > ");
                strcat(highlightChangeTwo,cDois);
                strcpy(highlightChangeThree,"TRUE");
            }
            return TRUE;
        }else{
            if(flagIfTwoArguments==1 && flagUseThree==0){
                strcpy(highlightChangeTwo,c);
                strcat(highlightChangeTwo," > ");
                strcat(highlightChangeTwo,cDois);
                strcpy(highlightChangeFour,"FALSE");
                flagUseThree = 1;
            }else if(flagIfTwoArguments==1 && flagUseThree==1){
                strcpy(highlightChangeThree,c);
                strcat(highlightChangeThree," > ");
                strcat(highlightChangeThree,cDois);
                strcpy(highlightChangeFive,"FALSE");
                flagUseThree = 0;
            }else{
                strcpy(highlightChangeTwo,c);
                strcat(highlightChangeTwo," > ");
                strcat(highlightChangeTwo,cDois);
                strcpy(highlightChangeThree,"FALSE");
            }
            return FALSE;
        }
    }else if(strcmp(neto->tipo,"MaiorIgual")==0){//maiorigual
        char *test;
        test = (char *) malloc(sizeof(char) * (strlen(neto->filhos[0]->valor)+1));
        strcpy(test, neto->filhos[0]->valor);
        strcpy(c, test);
        //auxUm = checkVar(neto->filhos[0]);
        auxDois = checkVar(neto->filhos[1]);
        //sprintf(c,"%f",auxUm);
        sprintf(cDois,"%d",auxDois);
        if(checkVar(neto->filhos[0])>=checkVar(neto->filhos[1])){
            if(flagIfTwoArguments==1 && flagUseThree==0){
                strcpy(highlightChangeTwo,c);
                strcat(highlightChangeTwo," >= ");
                strcat(highlightChangeTwo,cDois);
                strcpy(highlightChangeFour,"TRUE");
                flagUseThree = 1;
            }else if(flagIfTwoArguments==1 && flagUseThree==1){
                strcpy(highlightChangeThree,c);
                strcat(highlightChangeThree," >= ");
                strcat(highlightChangeThree,cDois);
                strcpy(highlightChangeFive,"TRUE");
                flagUseThree = 0;
            }else{
                strcpy(highlightChangeTwo,c);
                strcat(highlightChangeTwo," >= ");
                strcat(highlightChangeTwo,cDois);
                strcpy(highlightChangeThree,"TRUE");
            }
            return TRUE;
        }else{
            if(flagIfTwoArguments==1 && flagUseThree==0){
                strcpy(highlightChangeTwo,c);
                strcat(highlightChangeTwo," >= ");
                strcat(highlightChangeTwo,cDois);
                strcpy(highlightChangeFour,"FALSE");
                flagUseThree = 1;
            }else if(flagIfTwoArguments==1 && flagUseThree==1){
                strcpy(highlightChangeThree,c);
                strcat(highlightChangeThree," >= ");
                strcat(highlightChangeThree,cDois);
                strcpy(highlightChangeFive,"FALSE");
                flagUseThree = 0;
            }else{
                strcpy(highlightChangeTwo,c);
                strcat(highlightChangeTwo," >= ");
                strcat(highlightChangeTwo,cDois);
                strcpy(highlightChangeThree,"FALSE");
            }
            return FALSE;
        }
    }else if(strcmp(neto->tipo,"Menor")==0){ //menor
        char *test;
        test = (char *) malloc(sizeof(char) * (strlen(neto->filhos[0]->valor)+1));
        strcpy(test, neto->filhos[0]->valor);
        strcpy(c, test);
        //auxUm = checkVar(neto->filhos[0]);
        auxDois = checkVar(neto->filhos[1]);
        //sprintf(c,"%f",auxUm);
        sprintf(cDois,"%d",auxDois);
        if(checkVar(neto->filhos[0])<checkVar(neto->filhos[1])){
            if(flagIfTwoArguments==1 && flagUseThree==0){
                strcpy(highlightChangeTwo,c);
                strcat(highlightChangeTwo," < ");
                strcat(highlightChangeTwo,cDois);
                strcpy(highlightChangeFour,"TRUE");
                flagUseThree = 1;
            }else if(flagIfTwoArguments==1 && flagUseThree==1){
                strcpy(highlightChangeThree,c);
                strcat(highlightChangeThree," < ");
                strcat(highlightChangeThree,cDois);
                strcpy(highlightChangeFive,"TRUE");
                flagUseThree = 0;
            }else{
                strcpy(highlightChangeTwo,c);
                strcat(highlightChangeTwo," < ");
                strcat(highlightChangeTwo,cDois);
                strcpy(highlightChangeThree,"TRUE");
            }
            return TRUE;
        }else{
            if(flagIfTwoArguments==1 && flagUseThree==0){
                strcpy(highlightChangeTwo,c);
                strcat(highlightChangeTwo," < ");
                strcat(highlightChangeTwo,cDois);
                strcpy(highlightChangeFour,"FALSE");
                flagUseThree = 1;
            }else if(flagIfTwoArguments==1 && flagUseThree==1){
                strcpy(highlightChangeThree,c);
                strcat(highlightChangeThree," < ");
                strcat(highlightChangeThree,cDois);
                strcpy(highlightChangeFive,"FALSE");
                flagUseThree = 0;
            }else{
                strcpy(highlightChangeTwo,c);
                strcat(highlightChangeTwo," < ");
                strcat(highlightChangeTwo,cDois);
                strcpy(highlightChangeThree,"FALSE");
            }
            return FALSE;
        }
    }else if(strcmp(neto->tipo,"MenorIgual")==0){ //menorigual
        char *test;
        test = (char *) malloc(sizeof(char) * (strlen(neto->filhos[0]->valor)+1));
        strcpy(test, neto->filhos[0]->valor);
        strcpy(c, test);
        //auxUm = checkVar(neto->filhos[0]);
        auxDois = checkVar(neto->filhos[1]);
        //sprintf(c,"%f",auxUm);
        sprintf(cDois,"%d",auxDois);
        if(checkVar(neto->filhos[0])<=checkVar(neto->filhos[1])){
            if(flagIfTwoArguments==1 && flagUseThree==0){
                strcpy(highlightChangeTwo,c);
                strcat(highlightChangeTwo," <= ");
                strcat(highlightChangeTwo,cDois);
                strcpy(highlightChangeFour,"TRUE");
                flagUseThree = 1;
            }else if(flagIfTwoArguments==1 && flagUseThree==1){
                strcpy(highlightChangeThree,c);
                strcat(highlightChangeThree," <= ");
                strcat(highlightChangeThree,cDois);
                strcpy(highlightChangeFive,"TRUE");
                flagUseThree = 0;
            }else{
                strcpy(highlightChangeTwo,c);
                strcat(highlightChangeTwo," <= ");
                strcat(highlightChangeTwo,cDois);
                strcpy(highlightChangeThree,"TRUE");
            }
            return TRUE;
        }else{
            if(flagIfTwoArguments==1 && flagUseThree==0){
                strcpy(highlightChangeTwo,c);
                strcat(highlightChangeTwo," <= ");
                strcat(highlightChangeTwo,cDois);
                strcpy(highlightChangeFour,"FALSE");
                flagUseThree = 1;
            }else if(flagIfTwoArguments==1 && flagUseThree==1){
                strcpy(highlightChangeThree,c);
                strcat(highlightChangeThree," <= ");
                strcat(highlightChangeThree,cDois);
                strcpy(highlightChangeFive,"FALSE");
                flagUseThree = 0;
            }else{
                strcpy(highlightChangeTwo,c);
                strcat(highlightChangeTwo," <= ");
                strcat(highlightChangeTwo,cDois);
                strcpy(highlightChangeThree,"FALSE");
            }
            return FALSE;
        }
    }
}

void varDeclFunc(struct no* neto){
    char *c;
    if(strcmp(neto->filhos[2]->tipo,"ColorLit")==0){
        printf("varivael %s was set tipo %s\n", neto->filhos[1]->valor, neto->filhos[2]->tipo);
        c = (char *) malloc(sizeof(char) * (strlen(neto->filhos[0]->valor)+1));
        strcpy(c, neto->filhos[2]->tipo);
        strcpy(highlightChangeOne,c);
        strcpy(c, neto->filhos[1]->valor);
        strcpy(highlightChangeTwo,c);
        strcpy(c, neto->filhos[2]->filhos[0]->filhos[0]->filhos[0]->valor); //red 
        strcpy(highlightChangeThree,c);
        strcpy(c, neto->filhos[2]->filhos[0]->filhos[0]->filhos[1]->valor); //gree
        strcpy(highlightChangeFour,c);
        strcpy(c, neto->filhos[2]->filhos[0]->filhos[1]->valor); //blue
        strcpy(highlightChangeFive,c);
    }else{
        printf("varivael %s was set to %s, tipo %s\n", neto->filhos[1]->valor, neto->filhos[2]->valor, neto->filhos[2]->tipo);
        c = (char *) malloc(sizeof(char) * (strlen(neto->filhos[0]->valor)+1));
        strcpy(c, neto->filhos[2]->tipo);
        strcpy(highlightChangeOne,c);
        strcpy(c,neto->filhos[1]->valor);
        strcpy(highlightChangeTwo,c);
        strcpy(c,neto->filhos[2]->valor);
        strcpy(highlightChangeThree,c);
    }
    if(f<1){//falta mete lo a incrementar
        printf("dar highlights\n");
        //dar highlights a variavel que mude
    }else if(f==1){
        printf("alguma vez\n");
        flagVar=0;
        f=0;
    }
}

void highlightAux(){
    char *highlightReturn[0];
    glColor3f (1.0, 0.0, 0.0);
    glRasterPos2f(10, hightSize-100);
    printf("highlighttyp--------> %s\n", highlightType);
    if(strcmp(highlightType,"background")==0){
        strcat(highlightType," change color to: ");
        highlightReturn[0] = highlightType;
        while(*highlightReturn[0]){
            glutBitmapCharacter(GLUT_BITMAP_HELVETICA_10, *highlightReturn[0]++);
        }

        glColor3f(highlightChangeFloat[0], highlightChangeFloat[1], highlightChangeFloat[2]);
        glBegin(GL_QUADS);              // Each set of 4 vertices form a quad
        //pontos contra relogio
            glVertex2f(280,hightSize-95);   // canto superior esquerdo
            glVertex2f(300,hightSize-95); // canto superior direito
            glVertex2f(300,hightSize-105); 
            glVertex2f(280,hightSize-105);
        glEnd();
        glColor3f(1.0f, 1.0f, 1.0f);
        glLineWidth(1.0f);

        glBegin(GL_LINES);              // Each set of 4 vertices form a quad
            //pontos contra relogio
            glVertex2f(280,hightSize-95);   // canto superior esquerdo
            glVertex2f(300,hightSize-95); // canto superior direito
            glVertex2f(300,hightSize-95); // canto superior direito
            glVertex2f(300,hightSize-105); 
            glVertex2f(300,hightSize-105); 
            glVertex2f(280,hightSize-105);
            glVertex2f(280,hightSize-105);
            glVertex2f(280,hightSize-95);   // canto superior esquerdo
        glEnd();
    }else if(strcmp(highlightType,"fill")==0){
        strcat(highlightType," change color to: ");
        highlightReturn[0] = highlightType;
        while(*highlightReturn[0]){
            glutBitmapCharacter(GLUT_BITMAP_HELVETICA_10, *highlightReturn[0]++);
        }

        glColor3f(highlightChangeFloat[0]/255, highlightChangeFloat[1]/255, highlightChangeFloat[2]/255);
        glBegin(GL_QUADS);              // Each set of 4 vertices form a quad
        //pontos contra relogio
            glVertex2f(200,hightSize-95);   // canto superior esquerdo
            glVertex2f(220,hightSize-95); // canto superior direito
            glVertex2f(220,hightSize-105); 
            glVertex2f(200,hightSize-105);
        glEnd();
        glColor3f(1.0f, 1.0f, 1.0f);
        glLineWidth(1.0f);

        glBegin(GL_LINES);              // Each set of 4 vertices form a quad
            //pontos contra relogio
            glVertex2f(200,hightSize-95);   // canto superior esquerdo
            glVertex2f(220,hightSize-95); // canto superior direito
            glVertex2f(220,hightSize-95); // canto superior direito
            glVertex2f(220,hightSize-105); 
            glVertex2f(220,hightSize-105); 
            glVertex2f(200,hightSize-105);
            glVertex2f(200,hightSize-105);
            glVertex2f(200,hightSize-95);   // canto superior esquerdo
        glEnd();
        
    }else if(strcmp(highlightType,"stroke")==0){
        strcat(highlightType," was turn on.");
        highlightReturn[0] = highlightType;
        while(*highlightReturn[0]){
            glutBitmapCharacter(GLUT_BITMAP_HELVETICA_10, *highlightReturn[0]++);
        }
    }else if(strcmp(highlightType,"noStroke")==0){
        strcat(highlightType," was turn off.");
        highlightReturn[0] = highlightType;
        while(*highlightReturn[0]){
            glutBitmapCharacter(GLUT_BITMAP_HELVETICA_10, *highlightReturn[0]++);
        }
    }else if(strcmp(highlightType,"ellipse")==0){
        glRasterPos2f(10, hightSize-150);
        strcat(highlightType," was draw with:");
        highlightReturn[0] = highlightType;
        while(*highlightReturn[0]){
            glutBitmapCharacter(GLUT_BITMAP_HELVETICA_10, *highlightReturn[0]++);
        }

        glRasterPos2f(10, hightSize-140);
        strcpy(highlightType,"Coord of x: ");
        strcat(highlightType, highlightChangeOne);
        highlightReturn[0] = highlightType;
        while(*highlightReturn[0]){
            glutBitmapCharacter(GLUT_BITMAP_HELVETICA_10, *highlightReturn[0]++);
        }

        glRasterPos2f(10, hightSize-130);
        strcpy(highlightType,"Coord of y: ");
        strcat(highlightType, highlightChangeTwo);
        highlightReturn[0] = highlightType;
        while(*highlightReturn[0]){
            glutBitmapCharacter(GLUT_BITMAP_HELVETICA_10, *highlightReturn[0]++);
        }

        glRasterPos2f(10, hightSize-120);
        strcpy(highlightType,"Shape of width: ");
        strcat(highlightType, highlightChangeThree);
        highlightReturn[0] = highlightType;
        while(*highlightReturn[0]){
            glutBitmapCharacter(GLUT_BITMAP_HELVETICA_10, *highlightReturn[0]++);
        }

        glRasterPos2f(10, hightSize-110);
        strcpy(highlightType,"Shape of hight: ");
        strcat(highlightType, highlightChangeFour);
        highlightReturn[0] = highlightType;
        while(*highlightReturn[0]){
            glutBitmapCharacter(GLUT_BITMAP_HELVETICA_10, *highlightReturn[0]++);
        }

    }else if(strcmp(highlightType,"rect")==0){
        glRasterPos2f(10, hightSize-150);
        strcat(highlightType," was draw with:");
        highlightReturn[0] = highlightType;
        while(*highlightReturn[0]){
            glutBitmapCharacter(GLUT_BITMAP_HELVETICA_10, *highlightReturn[0]++);
        }

        glRasterPos2f(10, hightSize-140);
        strcpy(highlightType,"Top left corner X: ");
        strcat(highlightType, highlightChangeOne);
        highlightReturn[0] = highlightType;
        while(*highlightReturn[0]){
            glutBitmapCharacter(GLUT_BITMAP_HELVETICA_10, *highlightReturn[0]++);
        }

        glRasterPos2f(10, hightSize-130);
        strcpy(highlightType,"Top left corner Y: ");
        strcat(highlightType, highlightChangeTwo);
        highlightReturn[0] = highlightType;
        while(*highlightReturn[0]){
            glutBitmapCharacter(GLUT_BITMAP_HELVETICA_10, *highlightReturn[0]++);
        }

        glRasterPos2f(10, hightSize-120);
        strcpy(highlightType,"Width of the rect: ");
        strcat(highlightType, highlightChangeThree);
        highlightReturn[0] = highlightType;
        while(*highlightReturn[0]){
            glutBitmapCharacter(GLUT_BITMAP_HELVETICA_10, *highlightReturn[0]++);
        }

        glRasterPos2f(10, hightSize-110);
        strcpy(highlightType,"Hight of the rect: ");
        strcat(highlightType, highlightChangeFour);
        highlightReturn[0] = highlightType;
        while(*highlightReturn[0]){
            glutBitmapCharacter(GLUT_BITMAP_HELVETICA_10, *highlightReturn[0]++);
        }

    }else if(strcmp(highlightType,"triangle")==0){
        glRasterPos2f(10, hightSize-150);
        strcat(highlightType," was draw with:");
        highlightReturn[0] = highlightType;
        while(*highlightReturn[0]){
            glutBitmapCharacter(GLUT_BITMAP_HELVETICA_10, *highlightReturn[0]++);
        }

        glRasterPos2f(10, hightSize-140);
        strcpy(highlightType,"First corner's X: ");
        strcat(highlightType, highlightChangeOne);
        highlightReturn[0] = highlightType;
        while(*highlightReturn[0]){
            glutBitmapCharacter(GLUT_BITMAP_HELVETICA_10, *highlightReturn[0]++);
        }

        glRasterPos2f(10, hightSize-130);
        strcpy(highlightType,"First corner's Y: ");
        strcat(highlightType, highlightChangeTwo);
        highlightReturn[0] = highlightType;
        while(*highlightReturn[0]){
            glutBitmapCharacter(GLUT_BITMAP_HELVETICA_10, *highlightReturn[0]++);
        }

        glRasterPos2f(10, hightSize-120);
        strcpy(highlightType,"Second corner's X: ");
        strcat(highlightType, highlightChangeThree);
        highlightReturn[0] = highlightType;
        while(*highlightReturn[0]){
            glutBitmapCharacter(GLUT_BITMAP_HELVETICA_10, *highlightReturn[0]++);
        }

        glRasterPos2f(10, hightSize-110);
        strcpy(highlightType,"Second corner's Y: ");
        strcat(highlightType, highlightChangeFour);
        highlightReturn[0] = highlightType;
        while(*highlightReturn[0]){
            glutBitmapCharacter(GLUT_BITMAP_HELVETICA_10, *highlightReturn[0]++);
        }

        glRasterPos2f(10, hightSize-100);
        strcpy(highlightType,"Third corner's X: ");
        strcat(highlightType, highlightChangeFive);
        highlightReturn[0] = highlightType;
        while(*highlightReturn[0]){
            glutBitmapCharacter(GLUT_BITMAP_HELVETICA_10, *highlightReturn[0]++);
        }

        glRasterPos2f(10, hightSize-90);
        strcpy(highlightType,"Third corner's Y: ");
        strcat(highlightType, highlightChangeThree);
        highlightReturn[0] = highlightType;
        while(*highlightReturn[0]){
            glutBitmapCharacter(GLUT_BITMAP_HELVETICA_10, *highlightReturn[0]++);
        }
    }else if(strcmp(highlightType,"strokeWeight")==0){
        strcat(highlightType," change size to: ");
        strcat(highlightType, highlightChangeOne);
        highlightReturn[0] = highlightType;
        while(*highlightReturn[0]){
            glutBitmapCharacter(GLUT_BITMAP_HELVETICA_10, *highlightReturn[0]++);
        }
    }else if(strcmp(highlightType,"If")==0){
        glRasterPos2f(10, hightSize-150);
        strcat(highlightType," was enter. conditions:");
        highlightReturn[0] = highlightType;
        while(*highlightReturn[0]){
            glutBitmapCharacter(GLUT_BITMAP_HELVETICA_10, *highlightReturn[0]++);
        }
        if(flagIfTwoArguments==1){
            glRasterPos2f(10, hightSize-140);
            strcpy(highlightType,highlightChangeTwo);
            strcat(highlightType," ");
            strcat(highlightType,highlightChangeOne);
            strcat(highlightType," ");
            strcat(highlightType,highlightChangeThree);
            highlightReturn[0] = highlightType;
            while(*highlightReturn[0]){
                glutBitmapCharacter(GLUT_BITMAP_HELVETICA_10, *highlightReturn[0]++);
            }

            glRasterPos2f(10, hightSize-130);
            strcpy(highlightType,highlightChangeTwo);
            strcat(highlightType," is ");
            strcat(highlightType,highlightChangeFour);
            highlightReturn[0] = highlightType;
            while(*highlightReturn[0]){
                glutBitmapCharacter(GLUT_BITMAP_HELVETICA_10, *highlightReturn[0]++);
            }

            glRasterPos2f(10, hightSize-120);
            strcpy(highlightType,highlightChangeThree);
            strcat(highlightType," is ");
            strcat(highlightType,highlightChangeFive);
            highlightReturn[0] = highlightType;
            while(*highlightReturn[0]){
                glutBitmapCharacter(GLUT_BITMAP_HELVETICA_10, *highlightReturn[0]++);
            }

            glRasterPos2f(10, hightSize-110);
            strcpy(highlightType,highlightChangeFour);
            strcat(highlightType," ");
            strcat(highlightType,highlightChangeOne);
            strcat(highlightType," ");
            strcat(highlightType,highlightChangeFive);
            strcat(highlightType," outcome is: ");
            strcat(highlightType,highlightChangeSix);
            highlightReturn[0] = highlightType;
            while(*highlightReturn[0]){
                glutBitmapCharacter(GLUT_BITMAP_HELVETICA_10, *highlightReturn[0]++);
            }

            if(strcmp(highlightChangeSix,"TRUE")==0){
                glRasterPos2f(10, hightSize-100);
                strcpy(highlightType,"It will run the first block ('If').");
                highlightReturn[0] = highlightType;
                while(*highlightReturn[0]){
                    glutBitmapCharacter(GLUT_BITMAP_HELVETICA_10, *highlightReturn[0]++);
                }
            }else{
                glRasterPos2f(10, hightSize-100);
                strcpy(highlightType,"It will run the second block ('Else').");
                highlightReturn[0] = highlightType;
                while(*highlightReturn[0]){
                    glutBitmapCharacter(GLUT_BITMAP_HELVETICA_10, *highlightReturn[0]++);
                }
            }

            flagIfTwoArguments=0;
        }else{
            glRasterPos2f(10, hightSize-140);
            strcpy(highlightType,highlightChangeTwo);
            strcat(highlightType," is ");
            strcat(highlightType,highlightChangeThree);
            highlightReturn[0] = highlightType;
            while(*highlightReturn[0]){
                glutBitmapCharacter(GLUT_BITMAP_HELVETICA_10, *highlightReturn[0]++);
            }

            if(strcmp(highlightChangeThree,"TRUE")==0){
                glRasterPos2f(10, hightSize-130);
                strcpy(highlightType,"It will run the first block ('If').");
                highlightReturn[0] = highlightType;
                while(*highlightReturn[0]){
                    glutBitmapCharacter(GLUT_BITMAP_HELVETICA_10, *highlightReturn[0]++);
                }
            }else{
                glRasterPos2f(10, hightSize-130);
                strcpy(highlightType,"It will run the second block ('Else').");
                highlightReturn[0] = highlightType;
                while(*highlightReturn[0]){
                    glutBitmapCharacter(GLUT_BITMAP_HELVETICA_10, *highlightReturn[0]++);
                }
            }
        }
    }else if(strcmp(highlightType,"VarDecl")==0){
        strcpy(highlightType, "New variable ");
        strcat(highlightType,highlightChangeTwo);
        strcat(highlightType," is set as: ");
        if(strcmp(highlightChangeOne,"ColorLit")==0){
            int auxX = strlen(highlightType)*10;
            float colorAuxRed = atof(highlightChangeThree)/255;
            float colorAuxGreen = atof(highlightChangeFour)/255;
            float colorAuxBlue = atof(highlightChangeFive)/255;
            glColor3f(colorAuxRed,colorAuxGreen,colorAuxBlue);
            glBegin(GL_QUADS);              // Each set of 4 vertices form a quad
            //pontos contra relogio
                glVertex2f(auxX,hightSize-95);   // canto superior esquerdo
                glVertex2f(auxX+20,hightSize-95); // canto superior direito
                glVertex2f(auxX+20,hightSize-105); 
                glVertex2f(auxX,hightSize-105);
            glEnd();
            glColor3f(1.0f, 1.0f, 1.0f);
            glLineWidth(1.0f);

            glBegin(GL_LINES);              // Each set of 4 vertices form a quad
                //pontos contra relogio
                glVertex2f(auxX,hightSize-95);   // canto superior esquerdo
                glVertex2f(auxX+20,hightSize-95); // canto superior direito
                glVertex2f(auxX+20,hightSize-95); // canto superior direito
                glVertex2f(auxX+20,hightSize-105); 
                glVertex2f(auxX+20,hightSize-105); 
                glVertex2f(auxX,hightSize-105);
                glVertex2f(auxX,hightSize-105);
                glVertex2f(auxX,hightSize-95);   // canto superior esquerdo
            glEnd();
        }else{
            strcat(highlightType,highlightChangeThree);
        }
        highlightReturn[0] = highlightType;
        while(*highlightReturn[0]){
            glutBitmapCharacter(GLUT_BITMAP_HELVETICA_10, *highlightReturn[0]++);
        }
    }else if(strcmp(highlightType,"For")==0){
        glRasterPos2f(10, hightSize-140);
        strcpy(highlightType,"In this For:");
        highlightReturn[0] = highlightType;
        while(*highlightReturn[0]){
            glutBitmapCharacter(GLUT_BITMAP_HELVETICA_10, *highlightReturn[0]++);
        }

        glRasterPos2f(10, hightSize-130);
        strcpy(highlightType, highlightChangeOne);
        strcat(highlightType, " was use.");
        highlightReturn[0] = highlightType;
        while(*highlightReturn[0]){
            glutBitmapCharacter(GLUT_BITMAP_HELVETICA_10, *highlightReturn[0]++);
        }

        glRasterPos2f(10, hightSize-120);
        strcpy(highlightType, highlightChangeTwo);
        strcat(highlightType, " is the next step.");
        highlightReturn[0] = highlightType;
        while(*highlightReturn[0]){
            glutBitmapCharacter(GLUT_BITMAP_HELVETICA_10, *highlightReturn[0]++);
        }

        glRasterPos2f(10, hightSize-110);
        strcpy(highlightType, highlightChangeThree);
        strcat(highlightType, highlightChangeFour);
        highlightReturn[0] = highlightType;
        while(*highlightReturn[0]){
            glutBitmapCharacter(GLUT_BITMAP_HELVETICA_10, *highlightReturn[0]++);
        }

        glRasterPos2f(10, hightSize-100);
        strcpy(highlightType, highlightChangeFive);
        highlightReturn[0] = highlightType;
        while(*highlightReturn[0]){
            glutBitmapCharacter(GLUT_BITMAP_HELVETICA_10, *highlightReturn[0]++);
        }
    }
    return;
}

void varIntForFunc(struct no* neto){
    printf("dentro do for\n");
    if(flagFirstFor==0){
        printf("dentro do first for\n");
        begin = (int)checkVar(neto->filhos[0]->filhos[0]->filhos[1]);
        flagFirstFor=1;
        struct varInt * auxPointer = (struct varInt*) malloc(sizeof(varInt));
        forPointer = first;
        while(forPointer->next!=NULL){
            //printf("forPoint while %s\n", forPointer->id);
            forPointer = forPointer->next;
        }
        
        auxPointer->id = neto->filhos[0]->filhos[0]->filhos[0]->valor;
        strcpy(highlightChangeOne,auxPointer->id);
        //printf("passei id=%s\n",auxPointer->id);
        auxPointer->tipoVariavel = neto->filhos[0]->filhos[0]->filhos[1]->tipo;
        //printf("passei tipoVariavel=%s\n",auxPointer->tipoVariavel);
        auxPointer->valor = neto->filhos[0]->filhos[0]->filhos[1]->valor;
        strcpy(highlightChangeTwo,auxPointer->id);
        strcpy(startFor, auxPointer->valor);
        //printf("passei valor=%s\n",auxPointer->valor);
        auxPointer->next = NULL;
        forPointer->next = auxPointer;
    }
    struct no* netoIf;
    struct no* netoAux;
    if(strcmp(neto->filhos[1]->tipo,"Bloco")==0){
        forAux = neto->filhos[1]->num_filhos;
        netoAux=neto->filhos[1];
    }else{
        forAux = neto->num_filhos;
        netoAux=neto;
    } 
    printf("forAux = %d\n",forAux);
    if(flagForward==1){
        printf("flag ainda on \n");
        if(u<netoAux->num_filhos){
            netoIf = netoAux->filhos[u];
            printf("tipo do no do for %s\n", netoIf->tipo);
            printf("tipo do no neto do for %s\n", netoIf->filhos[0]->valor);
            if(strcmp(netoIf->tipo,"MethodDecl")==0){
                if(strcmp(netoIf->filhos[0]->valor,"background")==0){
                    strcpy(highlightType,"background");
                    replyZ = netoIf->filhos[0]->linha;
                    //codigo do background
                    background(netoIf);
                }
                else if(strcmp(netoIf->filhos[0]->valor,"fill")==0){
                    strcpy(highlightType,"fill");
                    replyZ = netoIf->filhos[0]->linha;
                    //codigo do fill
                    fill(netoIf);
                } 
                else if(strcmp(netoIf->filhos[0]->valor,"stroke")==0){
                    strcpy(highlightType,"stroke");
                    replyZ = netoIf->filhos[0]->linha;
                    strokeFlag = 1;
                    //codigo do stroke
                    stroke(netoIf);
                }
                else if(strcmp(netoIf->filhos[0]->valor,"noStroke")==0){
                    strcpy(highlightType,"noStroke");
                    replyZ = netoIf->filhos[0]->linha;
                    strokeFlag = 0;
                }
                else if(strcmp(netoIf->filhos[0]->valor,"ellipse")==0){
                    strcpy(highlightType,"ellipse");
                    replyZ = netoIf->filhos[0]->linha;
                    //codigo do ellipse
                    ellipse(netoIf);
                }
                else if(strcmp(netoIf->filhos[0]->valor,"rect")==0){
                    strcpy(highlightType,"rect");
                    replyZ = netoIf->filhos[0]->linha;
                    //codigo do quadrado
                    rect(netoIf);
                }
                else if(strcmp(netoIf->filhos[0]->valor,"triangle")==0){
                    strcpy(highlightType,"triangle");
                    replyZ = netoIf->filhos[0]->linha;
                    printf("linha do triangulo do if n-%d\n",netoIf->filhos[0]->linha);
                    //codigo do triangle
                    triangle(netoIf);
                }
                else if(strcmp(netoIf->filhos[0]->valor,"strokeWeight")==0){
                    strcpy(highlightType,"strokeWeight");
                    replyZ = netoIf->filhos[0]->linha;
                    //codigo do triangle
                    defaultLineWidth = checkVar(netoIf->filhos[1]);
                    char c[100];
                    sprintf(c,"%0.1f", defaultLineWidth);
                    strcpy(highlightChangeOne,c);
                }
            }else if(strcmp(netoIf->tipo,"If")==0){
                strcpy(highlightType,"If");
                printf("-----dentro do if--------\n");
                flagIf = 1;
                replyZ = netoIf->filhos[0]->linha;    
                ifElse(netoIf);
                printf("--------saiu do if-------\n");
            }
            glutSwapBuffers();
            /*else if(strcmp(netoIf->tipo,"If")==0){
                flagIf = 1;
                ifElse(netoIf);
                flagIf = 0;
            }*/
        }else if(u==netoAux->num_filhos){
            u=-1;
            printf("numero de filhos do for reachs\n");
            firstIf=0;
            auxFor(neto->filhos[0]->filhos[1], neto->filhos[0]->filhos[2]->filhos[1]);
        }
    }else{
        printf("-----------saiu do for-------------------\n");
        if(flagForForIf == 1){
            flagForForIf = 0;
        }else{
            flagFor = 0;
        }
        u=0;
        flagFirstFor = 0;
    }
    printf("flag do for forawrd %d\n", flagForward);
}

void auxFor(struct no* decision, struct no* step){
    //printf("dentro da decisão do For -> %s\n", decision->tipo);
    if(strcmp(decision->tipo,"Maior")==0){
        if(begin>(int)checkVar(decision->filhos[1])){
            auxForDo(step);
            if(begin>(int)checkVar(decision->filhos[1])){
                strcpy(highlightChangeFour," > ");
                strcat(highlightChangeFour,decision->filhos[1]->valor);
                strcat(highlightChangeFour," is TRUE");
                strcpy(highlightChangeFive, "We ran the block For again.");
                flagForward = 1;
            }else{
                strcpy(highlightChangeFour," > ");
                strcat(highlightChangeFour,decision->filhos[1]->valor);
                strcat(highlightChangeFour," is FALSE");
                strcpy(highlightChangeFive, "We leave this For.");
                begin = 0;
                strcpy(forPointer->next->valor,startFor);
                flagForward = 0;
            }
        }else{
            begin = 0;
            strcpy(forPointer->next->valor,startFor);
            flagForward = 0;
        }
    }else if(strcmp(decision->tipo,"MaiorIgual")==0){
        if(begin>=(int)checkVar(decision->filhos[1])){
            auxForDo(step);
            if(begin>=(int)checkVar(decision->filhos[1])){
                strcpy(highlightChangeFour," >= ");
                strcat(highlightChangeFour,decision->filhos[1]->valor);
                strcat(highlightChangeFour," is TRUE");
                strcpy(highlightChangeFive, "We ran the block For again.");
                flagForward = 1;
            }else{
                strcpy(highlightChangeFour," >= ");
                strcat(highlightChangeFour,decision->filhos[1]->valor);
                strcat(highlightChangeFour," is FALSE");
                strcpy(highlightChangeFive, "We leave this For.");
                begin = 0;
                strcpy(forPointer->next->valor,startFor);
                flagForward = 0;
            }
        }else{
            begin = 0;
            strcpy(forPointer->next->valor,startFor);
            flagForward = 0;
        }
    }else if(strcmp(decision->tipo,"Menor")==0){
        printf("begin %d menor que %s\n",begin,decision->filhos[1]->valor);
        if(begin<(int)checkVar(decision->filhos[1])){
            auxForDo(step);
            if(begin<(int)checkVar(decision->filhos[1])){
                strcpy(highlightChangeFour," < ");
                strcat(highlightChangeFour,decision->filhos[1]->valor);
                strcat(highlightChangeFour," is TRUE");
                strcpy(highlightChangeFive, "We ran the block For again.");
                flagForward = 1;
            }else{
                strcpy(highlightChangeFour," < ");
                strcat(highlightChangeFour,decision->filhos[1]->valor);
                strcat(highlightChangeFour," is FALSE");
                strcpy(highlightChangeFive, "We leave this For.");
                begin = 0;
                strcpy(forPointer->next->valor,startFor);
                flagForward = 0;
            }
        }else{
            begin = 0;
            strcpy(forPointer->next->valor,startFor);
            flagForward = 0;
        }
    }else if(strcmp(decision->tipo,"MenorIgual")==0){
        if(begin<=(int)checkVar(decision->filhos[1])){
            auxForDo(step);
            if(begin<=(int)checkVar(decision->filhos[1])){
                strcpy(highlightChangeFour," <= ");
                strcat(highlightChangeFour,decision->filhos[1]->valor);
                strcat(highlightChangeFour," is TRUE");
                strcpy(highlightChangeFive, "We ran the block For again.");
                flagForward = 1;
            }else{
                strcpy(highlightChangeFour," <= ");
                strcat(highlightChangeFour,decision->filhos[1]->valor);
                strcat(highlightChangeFour," is FALSE");
                strcpy(highlightChangeFive, "We leave this For.");
                begin = 0;
                strcpy(forPointer->next->valor,startFor);
                flagForward = 0;
            }
        }else{
            begin = 0;
            strcpy(forPointer->next->valor,startFor);
            flagForward = 0;
        }
    }
    //printf("forward %d\n", flagForward);
}

void auxForDo(struct no* step){
    char c[100];
    //printf("o que vai fazer no for %s\n", step->tipo);
    printf("begin antes %d\n", begin);
    if(strcmp(step->tipo,"Soma")==0){
        strcpy(highlightChangeOne,forPointer->next->id);
        strcat(highlightChangeOne," = ");
        strcat(highlightChangeOne,forPointer->next->valor);
        begin = begin + (int)checkVar(step->filhos[1]);
        sprintf(c,"%d",begin);
        strcpy(highlightChangeTwo,forPointer->next->id);
        strcat(highlightChangeTwo," = ");
        strcat(highlightChangeTwo,forPointer->next->id);
        strcat(highlightChangeTwo," + ");
        strcat(highlightChangeTwo,step->filhos[1]->valor);
        strcpy(highlightChangeThree,c);
        printf("é o pointer\n");
        strcpy(forPointer->next->valor,c);
    }else if(strcmp(step->tipo,"Subt")==0){
        strcpy(highlightChangeOne,forPointer->next->id);
        strcat(highlightChangeOne," = ");
        strcat(highlightChangeOne,forPointer->next->valor);
        begin = begin - (int)checkVar(step->filhos[1]);
        sprintf(c,"%d",begin);
        strcpy(highlightChangeTwo,forPointer->next->id);
        strcat(highlightChangeTwo," = ");
        strcat(highlightChangeTwo,forPointer->next->id);
        strcat(highlightChangeTwo," - ");
        strcat(highlightChangeTwo,step->filhos[1]->valor);
        strcpy(highlightChangeThree,c);
        strcpy(forPointer->next->valor,c);
    }else if(strcmp(step->tipo,"Multi")==0){
        strcpy(highlightChangeOne,forPointer->next->id);
        strcat(highlightChangeOne," = ");
        strcat(highlightChangeOne,forPointer->next->valor);
        begin = begin * (int)checkVar(step->filhos[1]);
        sprintf(c,"%d",begin);
        strcpy(highlightChangeTwo,forPointer->next->id);
        strcat(highlightChangeTwo," = ");
        strcat(highlightChangeTwo,forPointer->next->id);
        strcat(highlightChangeTwo," * ");
        strcat(highlightChangeTwo,step->filhos[1]->valor);
        strcpy(highlightChangeThree,c);
        strcpy(forPointer->next->valor,c);
    }else if(strcmp(step->tipo,"Div")==0){
        strcpy(highlightChangeOne,forPointer->next->id);
        strcat(highlightChangeOne," = ");
        strcat(highlightChangeOne,forPointer->next->valor);
        begin = begin / (int)checkVar(step->filhos[1]);
        sprintf(c,"%d",begin);
        strcpy(highlightChangeTwo,forPointer->next->id);
        strcat(highlightChangeTwo," = ");
        strcat(highlightChangeTwo,forPointer->next->id);
        strcat(highlightChangeTwo," / ");
        strcat(highlightChangeTwo,step->filhos[1]->valor);
        strcpy(highlightChangeThree,c);
        strcpy(forPointer->next->valor,c);
    }
    printf("begin depois %d\n", begin);
}
