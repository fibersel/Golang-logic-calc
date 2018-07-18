package main

import (
	"html/template"
	"net/http"
	"log"
	"strings"
	"encoding/json"
	"regexp"
)


type Operation int

type State int


const (
	Lbracket Operation = iota
	Rbracket
	Equality
	Denial
	Conjuction
	Disjuction
	Implication
	JDenial
	Sheffer_stroke
	XOR
)

var operators map[string]Operation = map[string]Operation {
	"(": Lbracket,
	")": Rbracket,
	"=": Equality,
	"¬": Denial,
	"•": Conjuction,
	"∨": Disjuction,
	"↓": JDenial,
	"|": Sheffer_stroke,
	"→": Implication,
	"⊕": XOR}


const (
	Ident State = iota
	Oper
	EOF
	Err
	H
)

type Lex struct {
	Type State
	op Operation
	name string
	value int
}

type Iden struct {
	name string
	value int
}

type Parser struct { 
	expr string
	syml string
	buf string
	index int
}


var Tabl_ident [100]Iden
var Ident_ctr int 
var lex * Lex
var parser * Parser
var Prog [] * Lex
var args []int


func NewParser(expr string) * Parser{
	Ident_ctr = 0
	parser := Parser{expr: expr, index: 0}
	parser.GetChar()
	return &parser
}


func (parser * Parser) GetChar(){
	if parser.index < len(parser.expr) {
		parser.syml = parser.expr[parser.index: parser.index+1]
		parser.index++
	} else {
		parser.syml = "$"
	}
}


func find(name string) int {
	for i := 0;i < Ident_ctr;i++ {
		if Tabl_ident[i].name == name {
			return i
		}
	}
	Tabl_ident[Ident_ctr] = Iden{name: name,
						value: 0}
	Ident_ctr++
	return Ident_ctr - 1 
}


func (parser * Parser) GetLex() * Lex{
	var CS State = H
	parser.buf = ""
	for {
		switch CS {
		case H:
			if strings.ContainsAny(parser.syml, " \n\t") {
				parser.GetChar()
			} else if strings.ContainsAny(parser.syml, "()=|" + 
								"¬"[0: 1] + 
								"•"[0: 1] + 
								"∨"[0: 1] +
								"↓"[0: 1] +
								"→"[0: 1] +
								"⊕"[0: 1]) {
				parser.buf += parser.syml
				CS = Oper
				parser.GetChar()
			} else if ok, _ := regexp.Match("\\w", []byte(parser.syml)); ok {
				parser.buf += parser.syml
				CS = Ident
				parser.GetChar()
			} else if parser.syml == "$" {
				return &Lex{Type: EOF, 
					op: 0, 
					name: "", 
					value: 0}
			} else {
				parser.buf += parser.syml
				parser.GetChar()
			}
		case Ident:
			if ok, _ := regexp.Match("[\\d\\w]", []byte(parser.syml)); ok {
				parser.buf += parser.syml
				parser.GetChar()
			} else {
				val := find(parser.buf)
				return &Lex{Type: Ident,
							op: 0,
							name: parser.buf,
							value: val}
			}
		case Oper:
			if strings.ContainsAny(parser.buf, "()=|¬•∨↓→⊕") {
				return &Lex{Type: Oper, 
						op: operators[parser.buf], 
						name: parser.buf, 
						value: 0}
			} else if len(parser.buf) == 3 {
				return &Lex{Type: Err,
						op: 0,
						name: "",
						value: 0}
			} else {
				parser.buf += parser.syml
				parser.GetChar()
			}
		case EOF:
			return &Lex{Type:EOF, 
				op: 0, 
				name: parser.buf,
				value: 0}
		case Err:
		}
	}
}


func shell() {
	lex = parser.GetLex()
	S()
	if lex.Type != EOF {
		log.Println("FATAL ERROR")
	}
	Prog = append(Prog, lex)
}


func S() {
	F()
	for lex.Type == Oper && lex.op == Equality {
		tmp_S := lex
		lex = parser.GetLex()
		F()
		Prog = append(Prog, tmp_S)
	}
}


func F() {
	T()
	for lex.Type == Oper && lex.op == Implication {
		tmp_F := lex
		lex = parser.GetLex()
		T()
		Prog = append(Prog, tmp_F)
	}
}


func T() {
	D()
	for lex.Type == Oper && lex.op == Disjuction ||
		lex.Type == Oper && lex.op == JDenial 	 ||
		lex.Type == Oper && lex.op == XOR {
		tmp_T := lex
		lex = parser.GetLex()
		D()
		Prog = append(Prog, tmp_T)
	}
}


func D(){
	L()
	for lex.Type == Oper && lex.op == Conjuction ||
		lex.Type == Oper && lex.op == Sheffer_stroke {
		tmp_D := lex
		lex = parser.GetLex()
		L()
		Prog = append(Prog, tmp_D)
	}
}



func L() {
	if lex.Type == Oper && lex.op == Lbracket {
		lex = parser.GetLex()
		S()
		if lex.Type == Oper && lex.op == Rbracket {
			lex = parser.GetLex()
		}
	} else if lex.Type == Oper && lex.op == Denial {
		tmp_L := lex
		lex = parser.GetLex()
		L()
		Prog = append(Prog, tmp_L)
	} else if lex.Type == Ident {
		Prog = append(Prog, lex)
		lex = parser.GetLex()
	}
}


type Ans struct {
	Rows int		 `json:"rows"`
	Columns []string `json:"clms"`
	Table [][]int	 `json:"table"`
}

func Pow(num int) int {
	base := 1
	for num > 0 {
		base *= 2
		num--
	}
	return base
}


func eq(op1, op2 int) int {
	if op1 == op2 {
		return 1
	}
	return 0
}


func denial(op int) int {
	if op == 0 {
		return 1
	}
	return 0
}

func execute() int {
	index := 0
	args = make([]int, 30)
	for Prog[index].Type != EOF {
		switch Prog[index].Type {
		case Ident:
			args = append(args, Tabl_ident[Prog[index].value].value)
		case Oper:
			l := len(args)
			op1, op2 := args[l-1], args[l-2]
			args = args[:l-2]
			switch Prog[index].op {
			case Equality:
				args = append(args, eq(op1, op2))
			case Conjuction:
				args = append(args, op1 * op2)
			case Disjuction:
				args = append(args, op1 + op2 - op1 * op2)
			case Denial:
				args = append(args, op2)
				args = append(args, denial(op1))
			case Implication:
				args = append(args, op1 + denial(op2) - op1 * denial(op2))
			case Sheffer_stroke:
				args = append(args, denial(op1 * op2))
			case XOR:
				args = append(args, (op1 + op2) % 2 )
			case JDenial:
				args = append(args, denial(op1 + op2 - op1 * op2))
			}
		}
		index++
	}
	return args[len(args) - 1]
}

func main() {

	tmpl, err := template.New("index.html").ParseFiles("index.html")
	if err != nil {
		log.Println("can not expand template", err)
	}

	http.Handle("/resources/", http.StripPrefix("/resources/", http.FileServer(http.Dir("resources"))))

	http.HandleFunc("/", func(w http.ResponseWriter, r *http.Request) {
		tmpl.Execute(w, nil)
	})

	http.HandleFunc("/req", func(w http.ResponseWriter, r *http.Request){

		if keys, ok := r.URL.Query()["expr"]; ok && len(keys) > 0 {
			log.Println(keys[0])
			parser = NewParser(keys[0])
			Prog = make([] * Lex, 0, 100)
			shell()

			combinations := Pow(Ident_ctr)
			header := make([]string, Ident_ctr, Ident_ctr)
			for j := 0; j < Ident_ctr; j++ {
				header[j] = Tabl_ident[j].name
			}

			ans := Ans{Rows: combinations, 
					Columns: header}


			for i := 0; Prog[i].Type != EOF; i++ {
				log.Println(Prog[i].name)
			}

			table := make([][]int, combinations, combinations)
			for i := 0; i < combinations; i++ {
				table[i] = make([]int, Ident_ctr + 1, Ident_ctr + 1) 
				for j := uint(0);j < uint(Ident_ctr);j++ {
					Tabl_ident[j].value = (i & (1 << j)) >> j
					table[i][j] = (i & (1 << j)) >> j
				}
				table[i][Ident_ctr] = execute()
			}
			
			ans.Table = table

			productsJson, _ := json.Marshal(ans)

			w.Header().Set("Content-Type", "application/json")
			w.WriteHeader(http.StatusOK)
			w.Write(productsJson)
		}
		
	})

	http.ListenAndServe(":8081", nil)

}