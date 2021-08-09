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
float defaultLineWidth = 1.0;
int strokeFlag = 1;
float strokeRed, strokeGreen, strokeBlue;
boolean paused = FALSE;
int firstFlag =1;
int z=1;
int t=0;
int f=0;
int switchDraw;
int setupAux;
int ifAux;

int varFlag = 0;
int varCount = 3;
struct varInt *dict;
struct varInt *first;
int flagIf = 0;
int flagVar = 0;

extern int num_linha;

void display();
void display2();
void display3();
void myMouseHandler(int button, int state, int x, int y);
float checkVar(struct no *varAux);
void timer(int value);
boolean ifValue(struct no *neto);
void varDeclFunc(struct no *neto);
//void idle();

void tabela_de_simbolos(struct no *root){
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
    dict = (struct varInt*) malloc(sizeof(varInt));
    first = (struct varInt*) malloc(sizeof(varInt));
    
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
            printf("teste erro %s\n", var);
            if(strcmp(var,"Color")==0){
                float colorRed = atof(no->filhos[i]->filhos[2]->filhos[0]->filhos[0]->filhos[0]->valor);
                float colorGreen = atof(no->filhos[i]->filhos[2]->filhos[0]->filhos[0]->filhos[1]->valor);
                float colorBlue = atof(no->filhos[i]->filhos[2]->filhos[0]->filhos[1]->valor);
                float colorFloatAux = (colorBlue+colorGreen+colorRed)/3;
                printf("color float value %f\n", colorFloatAux);
                char bufFloat[200];
                gcvt(colorFloatAux,10,bufFloat);
                char* finalColor = bufFloat;
                auxVar->valor = finalColor;
                printf("color value %s\n", auxVar->valor);
                printf("color value %s\n", finalColor);
            }else{
                auxVar->valor = no->filhos[i]->filhos[2]->valor;
                printf("non color value %s\n", auxVar->valor);
            }
            auxVar->next = NULL;
            if(varFlag==0){
                //printf("1st time^\n");
                varFlag=1;
                dict = auxVar;
                first = dict;
                //printf("id do first %s\n",first->id);
            }else{
                varCount++;
                //printf("seconds\n");
                dict->next = auxVar;
                //printf("seconds half\n");
                dict = dict->next;
                //printf("id do next %s\n",dict->next->id);
            }
            if(procurar_repetidos(no->filhos[i]->filhos[1]->valor, novo_elemento->funcdecl->variaveis, novo_elemento->funcdecl->n_parametros,0)==NULL){
                inserir_vardecl(no->filhos[i]->filhos[1]->valor, var, "null", &(novo_elemento->funcdecl->variaveis), no->filhos[i]->filhos[1]->linha, no->filhos[i]->filhos[1]->coluna);
                (novo_elemento->funcdecl->n_parametros)++;
            }
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

void timer(int value) {
    glutPostRedisplay();
    glutTimerFunc(1,timer,0);
}

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
            switchDraw=filhoDraw->num_filhos;
            if(z<filhoDraw->num_filhos && z>0){
                //printf("flag %d\n", firstFlag);
                netoDraw = filhoDraw->filhos[z];
                //printf("teste %s\n", netoDraw->tipo);
                if(strcmp(netoDraw->tipo,"MethodDecl")==0){
                    if(strcmp(netoDraw->filhos[0]->valor,"background")==0){
                        //codigo do background
                        background(netoDraw);
                    }
                    else if(strcmp(netoDraw->filhos[0]->valor,"fill")==0){
                        //codigo do fill
                        fill(netoDraw);
                    } 
                    else if(strcmp(netoDraw->filhos[0]->valor,"stroke")==0){
                        strokeFlag = 1;
                        //codigo do stroke
                        stroke(netoDraw);
                    }
                    else if(strcmp(netoDraw->filhos[0]->valor,"noStroke")==0){
                        strokeFlag = 0;
                    }
                    else if(strcmp(netoDraw->filhos[0]->valor,"ellipse")==0){
                        //codigo do ellipse
                        ellipse(netoDraw);
                    }
                    else if(strcmp(netoDraw->filhos[0]->valor,"rect")==0){
                        //codigo do quadrado
                        rect(netoDraw);
                    }
                    else if(strcmp(netoDraw->filhos[0]->valor,"triangle")==0){
                        //codigo do triangle
                        triangle(netoDraw);
                    }
                    else if(strcmp(netoDraw->filhos[0]->valor,"strokeWeight")==0){
                        //codigo do triangle
                        defaultLineWidth = checkVar(netoDraw->filhos[1]);
                    }
                }    
                else if(strcmp(netoDraw->tipo,"If")==0){
                    printf("dentro do if\n");
                    flagIf = 1;
                    ifElse(netoDraw);
                    printf("saiu do if\n");
                }else if(strcmp(netoDraw->tipo,"VarDecl")==0){
                    flagVar = 1;
                    printf("entrei \n");
                    varDeclFunc(netoDraw);
                } //fazer o que fiz nos ifs para aqui e assim incrementar para nao bloquear.
                glutSwapBuffers();
                //glutPostRedisplay();
            }else if(z==filhoDraw->num_filhos){
                z=0;
            }
        }
    }
    printf("display2\n");
    glViewport(wightSize,0,wightSize,hightSize);
    display2();
    /*glViewport(wightSize,0,wightSize,hightSize);
    glMatrixMode(GL_PROJECTION);
	glLoadIdentity();
    gluOrtho2D(0,wightSize,hightSize,0);

    display2();
    glutSwapBuffers();*/
   //glFlush();  // Render now
    
    printf("display3\n");
    glViewport(3*wightSize/2,0,3*wightSize/2,hightSize);
    display3();

}

void display2(){
    char *stringVar[varCount+1];
    char destAux[100];
    //printf("varCount = %d \n", varCount);
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
    printf("antes varcount= %d\n", varCount);
    for(int i=0;i<=varCount;i++){
        printf("i do for %d\n", i);
        glColor3f (1.0, 1.0, 0.0);
        if(i==0){
            glRasterPos2f(0, 10); //define position on the screen
            stringVar[i] = "Variaveis do sistema:";
            while(*stringVar[i]){
                glutBitmapCharacter(GLUT_BITMAP_8_BY_13, *stringVar[i]++);
            }
        }
        if(i<3){
            glRasterPos2f(0, 10+((i+1)*10)); //define position on the screen
        }else if(i==3){
            glRasterPos2f(0, 40+((i+1)*10)); //define position on the screen
            stringVar[i] = "Variaveis definidas:";
            while(*stringVar[i]){
                glutBitmapCharacter(GLUT_BITMAP_8_BY_13, *stringVar[i]++);
            }
            glRasterPos2f(0, 50+((i+1)*10)); //define position on the screen
        }else{
            glRasterPos2f(0, 50+((i+1)*10)); //define position on the screen
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
            sprintf(c,"%f", defaultLineWidth);
            strcat(destAux, c);
            stringVar[i] = destAux;
            while(*stringVar[i]){
                glutBitmapCharacter(GLUT_BITMAP_8_BY_13, *stringVar[i]++);
            }
        }else{
            //printf("id = %s\n",stringAux->id);
            //printf("i = %d\n",i);
            strcpy(destAux, "Int ");
            strcat(destAux, stringAux->id);
            strcat(destAux, " = ");
            strcat(destAux, stringAux->valor);
            stringVar[i] = destAux;
            //printf("dest %s\n",stringVar[i]);
            stringAux = stringAux->next;
            while(*stringVar[i]){
                glutBitmapCharacter(GLUT_BITMAP_8_BY_13, *stringVar[i]++);
            }
        }
    }
    printf("depois \n");
    glBegin(GL_QUADS);              // Each set of 4 vertices form a quad
        //pontos contra relogio
        glVertex2f(wightSize/2,hightSize-10);   // canto superior esquerdo
        glVertex2f(3*wightSize/4,hightSize-10); // canto superior direito
        glVertex2f(3*wightSize/4,hightSize-50); 
        glVertex2f(wightSize/2,hightSize-50);
    glEnd();
    
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
    int replyZ;

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
    replyZ=pos-switchDraw;
    if(z==switchDraw-1){
        printf("aint going in\n");
    }else{
    glBegin(GL_LINES);              // Each set of 4 vertices form a quad
        //pontos contra relogio
        glVertex2f(1,1+((replyZ+z)*15));   // canto superior esquerdo
        glVertex2f(300,1+((replyZ+z)*15)); // canto superior direito
        glVertex2f(300,1+((replyZ+z)*15)); 
        glVertex2f(300,11+((replyZ+z)*15));
        glVertex2f(300,11+((replyZ+z)*15));   // canto superior esquerdo
        glVertex2f(1,11+((replyZ+z)*15)); // canto superior direito
        glVertex2f(1,11+((replyZ+z)*15)); 
        glVertex2f(1,1+((replyZ+z)*15));
    glEnd();
    }
}

void background (struct no* neto){
    float red, blue, green;
    if(strcmp(neto->filhos[1]->tipo,"Virgula")==0){
        red = checkVar(neto->filhos[1]->filhos[0]->filhos[0])/255;
        blue = checkVar(neto->filhos[1]->filhos[0]->filhos[1])/255;
        green = checkVar(neto->filhos[1]->filhos[1])/255;
        //printf("3 argumentos \n");
    }
    else {
        //quando so tem um arguemento tipo 255
        red = checkVar(neto->filhos[1])/255.0;
        blue = checkVar(neto->filhos[1])/255.0;
        green = checkVar(neto->filhos[1])/255.0;
    }
    //printf("no background \n");
    glColor3f(red,blue,green); // Red 
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
        //printf("3 argumentos fill\n");
    }
    else {
        //quando so tem um arguemento tipo 255
        fillRed = checkVar(neto->filhos[1]);
        fillGreen = checkVar(neto->filhos[1]);
        fillBlue = checkVar(neto->filhos[1]);
        //printf("1 argumento fill\n");
    }
}

void rect(struct no* neto){
    float x,y,largura,altura; 
    struct no *auxRect = neto->filhos[1];
    x = checkVar(auxRect->filhos[0]->filhos[0]->filhos[0]);
    y = checkVar(auxRect->filhos[0]->filhos[0]->filhos[1]);
    largura = checkVar(auxRect->filhos[0]->filhos[1]);
    altura = checkVar(auxRect->filhos[1]);
    glColor3f(fillRed/255, fillGreen/255, fillBlue/255); // Red 
    /*if(strcmp(auxRect->filhos[0]->filhos[0]->filhos[1]->tipo, "Id")==0){
        printf("no if\n");
        dict = first;
        while(dict!=NULL){
            printf("no while\n");
            if(strcmp(auxRect->filhos[0]->filhos[0]->filhos[1]->valor,dict->id)==0){
                printf("y id %s\n", dict->id);
                printf("y valor %f\n", atof(dict->valor));
                y=atof(dict->valor);
            }
            dict = dict->next;
        }
    }else{
        printf("here\n");
        y = atof(auxRect->filhos[0]->filhos[0]->filhos[1]->valor);
    }
    glLineWidth(2.0);
    glBegin(GL_LINES);
    printf("inside lines \n");
    */

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
    float xp, yp, widthR, heightR;

    xp = checkVar(neto->filhos[1]->filhos[0]->filhos[0]->filhos[0]);
    yp = checkVar(neto->filhos[1]->filhos[0]->filhos[0]->filhos[1]);
    widthR = checkVar(neto->filhos[1]->filhos[0]->filhos[1]);
    heightR = checkVar(neto->filhos[1]->filhos[1]);

    glColor3f(fillRed,fillGreen,fillBlue);
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
        /*if(u==switchSetup){
            z++;    
            if(z==1){
                flagSetup=0;
            }
        }else{
            u++;
        }*/
        if(flagIf==0 && flagVar==0){
            if(z<switchDraw){
                if(x>(wightSize+(wightSize/4)) && x<(wightSize+(3*wightSize/8)) && y>(hightSize-50) && y<(hightSize-10)){
                    z++;
                }
            }else{
                z=1;
            }
        }else if(flagIf==1){
            if(t<ifAux){
                if(x>(wightSize+(wightSize/4)) && x<(wightSize+(3*wightSize/8)) && y>(hightSize-50) && y<(hightSize-10)){
                    t++;
                }
            }else{
                t=1;
            }
        }else if(flagVar==1){
            if(f<1){
                if(x>(wightSize+(wightSize/4)) && x<(wightSize+(3*wightSize/8)) && y>(hightSize-50) && y<(hightSize-10)){
                    f++;
                }
            }else{
                f=0;
            }
        }
        //printf("clickou no button direito\n");
    }else if(button==GLUT_LEFT_BUTTON && state==GLUT_DOWN){
        /*if(z==1 && u>1){
            u--;
        }else if(z>1){
            z--;
        }*/
        if(z>1){
            z--;
        }
        glutSwapBuffers();
        //printf("clickou no button esquerdo\n");
    }
    printf("z->%d\n",z);
    printf("t->%d\n",t);
}

void triangle(struct no* neto){
    //printf("trinaglo\n");
    float primX, primY, segX, segY, tercX, tercY;
    struct no* auxNeto = neto->filhos[1];
    primX = checkVar(auxNeto->filhos[0]->filhos[0]->filhos[0]->filhos[0]->filhos[0]);
    primY = checkVar(auxNeto->filhos[0]->filhos[0]->filhos[0]->filhos[0]->filhos[1]);
    segX = checkVar(auxNeto->filhos[0]->filhos[0]->filhos[0]->filhos[1]);    
    segY = checkVar(auxNeto->filhos[0]->filhos[0]->filhos[1]);
    tercX = checkVar(auxNeto->filhos[0]->filhos[1]);
    tercY = checkVar(auxNeto->filhos[1]);

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
                printf("y id %s\n", temp->id);
                printf("y valor %s\n", temp->valor);
                return(atof(temp->valor));
            }
            temp = temp->next;
        }
    }else if(strcmp(varAux->tipo, "Div")==0){
        //printf("div\n");
        expA = checkVar(varAux->filhos[0]);
        expB = checkVar(varAux->filhos[1]);
        return(expA/expB);
    }else if(strcmp(varAux->tipo, "Multi")==0){
        //printf("multi\n");
        expA = checkVar(varAux->filhos[0]);
        expB = checkVar(varAux->filhos[1]);
        return(expA*expB);
    }else if(strcmp(varAux->tipo, "Soma")==0){
        //printf("soma\n");
        expA = checkVar(varAux->filhos[0]);
        expB = checkVar(varAux->filhos[1]);
        return(expA+expB);
    }else if(strcmp(varAux->tipo, "Subt")==0){
        //printf("subt\n");
        expA = checkVar(varAux->filhos[0]);
        expB = checkVar(varAux->filhos[1]);
        return(expA-expB);
    }else{
        //printf("var int\n");
        return(atof(varAux->valor));
    }
    return;
}

void ifElse(struct no* neto){
    boolean ifTrue = ifValue(neto->filhos[0]); //resolver o valor do if
    if(ifTrue){ //se a condição for verdadeira
        struct no* netoIf;
        struct no* netoAux;
        if(strcmp(neto->filhos[1]->tipo,"Bloco")==0){
            ifAux = neto->filhos[1]->num_filhos;
            netoAux=neto->filhos[1];
        }else{
            ifAux = neto->num_filhos;
            netoAux=neto;
        }    
        if(t<netoAux->num_filhos){
            netoIf = netoAux->filhos[t];
            printf("tipo do no do if %s\n", netoIf->tipo);
            printf("tipo do no neto do if %s\n", netoIf->filhos[0]->valor);
            if(strcmp(netoIf->tipo,"MethodDecl")==0){
                if(strcmp(netoIf->filhos[0]->valor,"background")==0){
                    //codigo do background
                    background(netoIf);
                }
                else if(strcmp(netoIf->filhos[0]->valor,"fill")==0){
                    //codigo do fill
                    fill(netoIf);
                } 
                else if(strcmp(netoIf->filhos[0]->valor,"stroke")==0){
                    strokeFlag = 1;
                    //codigo do stroke
                    stroke(netoIf);
                }
                else if(strcmp(netoIf->filhos[0]->valor,"noStroke")==0){
                    strokeFlag = 0;
                }
                else if(strcmp(netoIf->filhos[0]->valor,"ellipse")==0){
                    //codigo do ellipse
                    ellipse(netoIf);
                }
                else if(strcmp(netoIf->filhos[0]->valor,"rect")==0){
                    //codigo do quadrado
                    rect(netoIf);
                }
                else if(strcmp(netoIf->filhos[0]->valor,"triangle")==0){
                    //codigo do triangle
                    triangle(netoIf);
                }
                else if(strcmp(netoIf->filhos[0]->valor,"strokeWeight")==0){
                    //codigo do triangle
                    defaultLineWidth = checkVar(netoIf->filhos[1]);
                }
            }
            glutSwapBuffers();
            /*else if(strcmp(netoIf->tipo,"If")==0){
                flagIf = 1;
                ifElse(netoIf);
                flagIf = 0;
            }*/
        }else if(t==netoAux->num_filhos){
            t=0;
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
                    //codigo do background
                    background(netoIf);
                }
                else if(strcmp(netoIf->filhos[0]->valor,"fill")==0){
                    //codigo do fill
                    fill(netoIf);
                } 
                else if(strcmp(netoIf->filhos[0]->valor,"stroke")==0){
                    strokeFlag = 1;
                    //codigo do stroke
                    stroke(netoIf);
                }
                else if(strcmp(netoIf->filhos[0]->valor,"noStroke")==0){
                    strokeFlag = 0;
                }
                else if(strcmp(netoIf->filhos[0]->valor,"ellipse")==0){
                    //codigo do ellipse
                    ellipse(netoIf);
                }
                else if(strcmp(netoIf->filhos[0]->valor,"rect")==0){
                    //codigo do quadrado
                    rect(netoIf);
                }
                else if(strcmp(netoIf->filhos[0]->valor,"triangle")==0){
                    //codigo do triangle
                    triangle(netoIf);
                }
                else if(strcmp(netoIf->filhos[0]->valor,"strokeWeight")==0){
                    //codigo do triangle
                    defaultLineWidth = checkVar(netoIf->filhos[1]);
                }
            }
            glutSwapBuffers();
            /*else if(strcmp(netoIf->tipo,"If")==0){
                flagIf = 1;
                ifElse(netoIf);
                flagIf = 0;
            }*/
        }else if(t==netoAux->num_filhos){
            t=0;
            flagIf=0;
        }
        //no fim mudar a flag
        //flagIf=0;
    }
}

boolean ifValue(struct no* neto){
    //cada um tem de ter um if que retorna false ou true
    if(strcmp(neto->tipo,"And")==0){//and
        if(ifValue(neto->filhos[0]) && ifValue(neto->filhos[1])){
            return TRUE;
        }else{
            return FALSE;
        }
    }else if(strcmp(neto->tipo,"Or")==0){//or
        if(ifValue(neto->filhos[0]) || ifValue(neto->filhos[1])){
            return TRUE;
        }else{
            return FALSE;
        }
    }else if(strcmp(neto->tipo,"Eq")==0){//eq
        if(checkVar(neto->filhos[0])==checkVar(neto->filhos[1])){
            return TRUE;
        }else{
            return FALSE;
        }
    }else if(strcmp(neto->tipo,"Diferente")==0){//diferente
        if(checkVar(neto->filhos[0])!=checkVar(neto->filhos[1])){
            return TRUE;
        }else{
            return FALSE;
        }
    }else if(strcmp(neto->tipo,"Maior")==0){//maior
        if(checkVar(neto->filhos[0])>checkVar(neto->filhos[1])){
            return TRUE;
        }else{
            return FALSE;
        }
    }else if(strcmp(neto->tipo,"MaiorIgual")==0){//maiorigual
        if(checkVar(neto->filhos[0])>=checkVar(neto->filhos[1])){
            return TRUE;
        }else{
            return FALSE;
        }
    }else if(strcmp(neto->tipo,"Menor")==0){ //menor
        if(checkVar(neto->filhos[0])<checkVar(neto->filhos[1])){
            return TRUE;
        }else{
            return FALSE;
        }
    }else if(strcmp(neto->tipo,"MenorIgual")==0){ //menorigual
        if(checkVar(neto->filhos[0])<=checkVar(neto->filhos[1])){
            return TRUE;
        }else{
            return FALSE;
        }
    }
}

void varDeclFunc(struct no* neto){
    while (f<1){//falta mete lo a incrementar 
        //dar highlights a variavel que mude
        printf("is highlighted %s\n", neto->filhos[2]->tipo);
        z++;
        f=1;
        flagVar=0;
    }if(f==1){
        printf("alguma vez\n");
        flagVar=0;
        f=0;
    }
}