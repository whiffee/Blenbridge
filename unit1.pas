{  Blenbridge version 1.21
   written by Gary Bollenbach
   June 23, 2020


***** BEGIN GPL LICENSE BLOCK *****
#
# This program is free software; you can redistribute it and/or
# modify it under the terms of the GNU General Public License
# as published by the Free Software Foundation; either version 3
# of the License, or (at your option) any later version.
#
# This program is distributed in the hope that it will be useful,
# but WITHOUT ANY WARRANTY; without even the implied warranty of
# MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
# GNU General Public License for more details.
#
# You should have received a copy of the GNU General Public License
# along with this program; if not, write to the Free Software Foundation,
# Inc., 59 Temple Place - Suite 330, Boston, MA  02111-1307, USA.
#
# ***** END GPL LICENSE BLOCK *****
# --------------------------------------------------------------------------
 }


unit Unit1;

{$mode objfpc}{$H+}

interface

uses
  Classes, SysUtils, FileUtil, Forms, Controls, Graphics, Dialogs, StdCtrls,
  MaskEdit, ExtCtrls, Menus, Math, IniFiles, SynEdit, LCLintf, StrUtils, CRT;

type

  { TForm1 }

  TForm1 = class(TForm)
    Button1: TButton;
    Button2: TButton;
    Button3: TButton;
    Button7: TButton;
    Button8: TButton;
    Button9: TButton;
    Image1: TImage;
    Label1: TLabel;
    Label3: TLabel;
    Label4: TLabel;
    Label5: TLabel;
    Label6: TLabel;
    Label7: TLabel;
    MainMenu1: TMainMenu;
    MaskEdit1: TMaskEdit;
    MaskEdit2: TMaskEdit;
    Memo1: TMemo;
    Memo2: TMemo;
    Memo3: TMemo;
    MenuItem1: TMenuItem;
    MenuItem10: TMenuItem;
    MenuItem11: TMenuItem;
    MenuItem12: TMenuItem;
    MenuItem13: TMenuItem;
    MenuItem16: TMenuItem;
    MenuItem17: TMenuItem;
    MenuItem18: TMenuItem;
    MenuItem2: TMenuItem;
    MenuItem3: TMenuItem;
    MenuItem4: TMenuItem;
    MenuItem5: TMenuItem;
    MenuItem6: TMenuItem;
    MenuItem7: TMenuItem;
    MenuItem8: TMenuItem;
    MenuItem9: TMenuItem;
    OpenDialog1: TOpenDialog;
    Panel1: TPanel;
    Panel2: TPanel;
    SaveDialog1: TSaveDialog;
    StaticText1: TStaticText;
    SynEdit1: TSynEdit;
    Timer1: TTimer;
    procedure Button1Click(Sender: TObject);
    procedure Button2Click(Sender: TObject);
    procedure Button3Click(Sender: TObject);
    procedure Button4Click(Sender: TObject);
    procedure Button6Click(Sender: TObject);
    procedure Button7Click(Sender: TObject);
    procedure Button8Click(Sender: TObject);
    procedure FormCreate(Sender: TObject);
    procedure FormDestroy(Sender: TObject);
    procedure FormShow(Sender: TObject);
    procedure MenuItem10Click(Sender: TObject);
    procedure MenuItem11Click(Sender: TObject);
    procedure MenuItem12Click(Sender: TObject);
    procedure MenuItem13Click(Sender: TObject);
    procedure MenuItem14Click(Sender: TObject);
    procedure MenuItem15Click(Sender: TObject);
    procedure MenuItem16Click(Sender: TObject);
    procedure MenuItem17Click(Sender: TObject);
    procedure MenuItem18Click(Sender: TObject);
    procedure MenuItem4Click(Sender: TObject);
    procedure MenuItem5Click(Sender: TObject);
    procedure MenuItem6Click(Sender: TObject);
    procedure MenuItem7Click(Sender: TObject);
    procedure MenuItem8Click(Sender: TObject);
    procedure MenuItem9Click(Sender: TObject);
    procedure PlyWriteVtk(Sender: TObject);
    function GetToken(aString, SepChar: string; TokenNum: Byte): string;
    function Anglesep(x1, y1, z1, x2, y2, z2: Double): double;
    procedure SearchforEdge(Sender: TObject);
    procedure GetCellDimensions(Sender: TObject);
    procedure MyShowMessage(Const Fmt : String; const Args : Array of const);
    procedure VtkWritePly(Sender: TObject);
    procedure ProcessEightBlobs(Sender: TObject);
    procedure Timer1StartTimer(Sender: TObject);
    procedure Timer1StopTimer(Sender: TObject);
    procedure Timer1Timer(Sender: TObject);
    procedure Ply3WriteVtk(Sender: TObject);
    procedure Searchfor3Edge(Sender: TObject);
    procedure Process3EightBlobs(Sender: TObject);
    function GetWinding(i1, i2, i3, i4 : String): Integer;
    procedure Ply4WriteVtk(Sender: TObject);
    procedure WritePly4Faces(Sender: TObject);
    procedure WritePly3Faces(Sender: TObject);
    function FindEdgeSite(s1, s2, s3, s4, s5, s6 : String): string;
    procedure WritePlyTri(Sender: TObject);
    function CheckVol(i1, i2, i3, i4 : Integer) : Double;
    procedure AdjustFont(Sender: TObject);
    procedure EnforceVerdictWinding(Sender: TObject);
    function Crossp(w1, w2, w3, x1, x2, x3: Double): String;
    function Dotp(y1, y2, y3, z1, z2, z3: Double): Double;
    procedure ResizeEvent(Sender: TObject);
    procedure Button9Click(Sender: TObject);

  private
    { private declarations }
  public
    { public declarations }
    mycurrentDir2, myvar3, myvar4, a1adj, a2adj, a3adj, a4adj, tempblob,
    outfilename: string;
    numberofverts, numberoffaces, normalno, numberofcells, radfac,
     ElapsedT, F3, F, eightblobscounter, tbp, ww, hh, wf : Integer;
     xside, yside, zside, sidecume, vertlistf, hopper1, wooda,
      Trigarray, Trigarray2, finalindex, blobsworth, dupecheck, oneedge,
     twoedge, dupes, dupe8, vertlists, luniverse, output, eightblobsl,
      eightblobs3, eightblobsf : TStringlist;
     {Stringlists are performing well, even without the try..finally
     blocks. However, they are slow compared with arrays, and I got a nice
     speedup when I got rid of eightblobs for its array counterpart. }
    Numarrayx, Numarrayy, Numarrayz, centroidx, centroidy, centroidz,
    longvec : array [0..3000000] of Double;
    curedgea1, eightblobs : array [0..5000000] of  String;
    opptemp : array [0..100] of String;
    separray, septemp, copa, m1 : array [0..102] of Double;
    {m1 is the array for objects: form, memo, button, label, checkbox, mask edit:
    fm1, m1, m3, b1, b2, b3, b4, b5, b6,
    la1, la2, la3, la4, cb1, me1, and the attributes H, W, L, T }
    fc : array [0..4] of Double;
    formsyze, inivaluef : Single;
    vtkout, plyout : Boolean;
    pic : Double;
    button9count, savesize : Integer;

  end;

var
  Form1: TForm1;

implementation

{$R *.lfm}

{ TForm1 }

procedure TForm1.Button1Click(Sender: TObject);
begin
  Panel2.Visible := false;
end;

procedure TForm1.Button2Click(Sender: TObject);
begin
   Memo2.Visible := false;
   Button2.Visible := false;

end;

procedure TForm1.Button3Click(Sender: TObject);

begin
  Panel1.Visible := false;
end;

procedure TForm1.Button4Click(Sender: TObject);
begin

  {Application.terminate;
  while not Application.Terminated do
  Application.ProcessMessages;}
   FormDestroy(Sender);
end;

procedure TForm1.AdjustFont(Sender: TObject);

begin
  SynEdit1.Font.Size := SynEdit1.Font.Size  + tbp; Memo3.Font.Size := Memo3.Font.Size + tbp;
  Memo1.Font.Size := Memo1.Font.Size  + tbp; Button2.Font.Size := Button2.Font.Size + tbp;
  Button3.Font.Size := Button3.Font.Size  + tbp; StaticText1.Font.Size := StaticText1.Font.Size + tbp;
   Button1.Font.Size := Button1.Font.Size + tbp;
  Label5.Font.Size := Label5.Font.Size  + tbp;
  Label3.Font.Size := Label3.Font.Size  + tbp; MaskEdit1.Font.Size := MaskEdit1.Font.Size + tbp;
  Label4.Font.Size := Label4.Font.Size + tbp;MaskEdit2.Font.Size := MaskEdit2.Font.Size + tbp;
  Label6.Font.Size := Label6.Font.Size + tbp;Button7.Font.Size := Button7.Font.Size + tbp;
  Button8.Font.Size := Button8.Font.Size + tbp;Label1.Font.Size := Label1.Font.Size + tbp;
  Memo2.Font.Size := Memo2.Font.Size + tbp;
end;

procedure TForm1.Button6Click(Sender: TObject);
begin
  if myvar3 <> '' then
  Label5.visible := true;
  Application.ProcessMessages;
  VtkWritePly(Sender);
end;

procedure TForm1.Button7Click(Sender: TObject);
begin
  tbp := -1;
  AdjustFont(Sender);
end;

procedure TForm1.Button8Click(Sender: TObject);
begin
  tbp := 1;
  AdjustFont(Sender);
end;

procedure TForm1.FormCreate(Sender: TObject);
begin

end;

procedure TForm1.Button9Click(Sender: TObject);
begin

  ResizeEvent(Sender);
end;

procedure TForm1.FormDestroy(Sender: TObject);
var
    myINI : TINIFile;
begin


   myINI := TINIFile.Create(ExtractFilePath(Application.EXEName) +
   'blenbridge.ini');

   with myINI do begin
      WriteInteger('Section', 'Ident', savesize);
   end;
   myINI.Free;
  { close1 := close1 +1; }
  { Button4.Color := clYellow;
   Button4.Color := $007E6E09; }
  { Button4.Color := RGBToColor(255, 251, 148);
   Button4.Font.Style := [fsBold];
   Button4.Caption := 'Quit?';  }
  { if close1 = 1 then begin }
 { Delay(600); }
   Halt(0);
   {end;}
end;



procedure TForm1.FormShow(Sender: TObject);
var
myINI : TINIFile;
begin
   myINI := TINIFile.Create(ExtractFilePath(Application.EXEName) +
  'blenbridge.ini');

   inivaluef := myINI.ReadInteger('Section', 'Ident', 0);
   if inivaluef = 0 then savesize := 0;
   if inivaluef = 1 then savesize := 1;
   if inivaluef = 2 then savesize := 2;
   if inivaluef = 3 then savesize := 3;
   if inivaluef = 4 then savesize := 4;
   if inivaluef = 5 then savesize := 5;
   if inivaluef = 6 then savesize := 6;
   if inivaluef = 7 then savesize := 7;
   if savesize = 0 then pic := 0.75 ;
   if savesize = 1 then pic := 0.7875;
   if savesize = 2 then pic := 0.8682;
   if savesize = 3 then pic := 0.9116;
   if savesize = 4 then pic := 0.9572;
   if savesize = 5 then pic := 1.005;
   if savesize = 6 then pic := 1.055;
   if savesize = 7 then pic := 1.108;


   button9count := 0;
   Label5.Font.Color := clGreen;
  Timer1.enabled := false;

  {pic := 0.75; }
  hh := Screen.Height;
  ww := Screen.Width;
  wf := 2700;
  Form1.Height := Round(hh/2*pic);
  Form1.Width := Round(ww/2*pic);
  Memo3.Height := Round(hh/22*pic); Memo3.Width := Round(ww/2.055*pic);
  Memo3.Left := Round(ww/150*pic); Memo3.Top := Round(hh/32*pic);
  SynEdit1.Height := Round(hh/2.9*pic); SynEdit1.Width := Round(ww/2.055*pic);
  SynEdit1.Left := Round(ww/150*pic); SynEdit1.Top := Round(hh/12*pic);
  Panel1.Height := Round(hh/6*pic); Panel1.Width := Round(ww/8*pic);
  Panel1.Left := Round(hh/3.0*pic); Panel1.Top := Round(hh/15*pic);
  Button3.Height := Round(hh/40*pic); Button3.Width := Round(ww/26*pic);
  Button3.Left := Round(hh/14.5*pic); Button3.Top := Round(hh/7.7*pic);
  MaskEdit2.Height := Round(hh/40*pic); MaskEdit2.Width := Round(ww/35*pic);
  MaskEdit2.Left := Round(hh/40*pic); MaskEdit2.Top := Round(hh/14*pic);
  Label6.Height := Round(hh/30*pic); Label6.Width := Round(ww/25*pic);
  Label6.Left := Round(hh/45*pic); Label6.Top := Round(hh/10*pic);
  Label1.Height := Round(hh/30*pic); Label1.Width := Round(ww/25*pic);
  Label1.Left := Round(hh/9.5*pic); Label1.Top := Round(hh/10*pic);
  Button8.Height := Round(hh/45*pic); Button8.Width := Round(hh/45*pic);
  Button8.Left := Round(hh/6.5*pic); Button8.Top := Round(hh/14*pic);
  Button7.Height := Round(hh/45*pic); Button7.Width := Round(hh/45*pic);
  Button7.Left := Round(hh/9*pic); Button7.Top := Round(hh/14*pic);
  Button1.Height := Round(hh/45*pic); Button1.Width := Round(hh/15*pic);
  Button1.Left := Round(hh/11*pic); Button1.Top := Round(hh/4*pic);
  MaskEdit1.Height := Round(hh/40*pic); MaskEdit1.Width := Round(ww/35*pic);
  MaskEdit1.Left := Round(hh/40*pic); MaskEdit1.Top := Round(hh/50*pic);
  Label3.Height := Round(hh/30*pic); Label3.Width := Round(ww/25*pic);
  Label3.Left := Round(hh/45*pic); Label3.Top := Round(hh/22*pic);
  Panel2.Height := Round(hh/3.5*pic); Panel2.Width := Round(ww/6.5*pic);
  Panel2.Left := Round(hh/3.4*pic); Panel2.Top := Round(hh/25*pic);
  Image1.Height := Round(hh/6*pic); Image1.Width := Round(ww/5*pic);
  Image1.Left := Round(hh/25.5*pic); Image1.Top := Round(hh/55*pic);
  StaticText1.Height := Round(hh/30*pic); StaticText1.Width := Round(ww/5*pic);
  StaticText1.Left := Round(hh/20.2*pic); StaticText1.Top := Round(hh/9.5*pic);
  Memo1.Height := Round(hh/12*pic); Memo1.Width := Round(ww/5*pic);
  Memo1.Left := Round(hh/40*pic); Memo1.Top := Round(hh/6.6*pic);
  Memo2.Height := Round(hh/2.5*pic); Memo2.Width := Round(ww/2.055*pic);
  Memo2.Left := Round(ww/150*pic); Memo2.Top := Round(hh/32*pic);
  Button2.Height := Round(hh/45*pic); Button2.Width := Round(hh/8*pic);
  Button2.Left := Round(hh/2.9*pic); Button2.Top := Round(hh/2.3*pic);
  Label5.Height := Round(hh/30*pic); Label5.Width := Round(ww/2.5*pic);
  Label5.Left := Round(hh/2.5*pic); Label5.Top := Round(hh/65*pic);
  Button9.Height := Round(hh/45*pic); Button9.Width := Round(hh/45*pic);
  Button9.Left := Round(hh/7*pic); Button9.Top := Round(hh/50*pic);
  Label7.Height := Round(hh/30*pic); Label7.Width := Round(ww/2.5*pic);
  Label7.Left := Round(hh/8.6*pic); Label7.Top := Round(hh/22*pic);

  SynEdit1.Font.Size := Round(wf/230*pic);
  Memo3.Font.Size := Round(wf/230*pic);
  Panel1.Font.Size := Round(wf/280*pic);
  MaskEdit1.Font.Size := Round(wf/300*pic);
  MaskEdit2.Font.Size := Round(wf/300*pic);
  Label6.Font.Size := Round(wf/310*pic);
  Label1.Font.Size := Round(wf/310*pic);
  Label3.Font.Size := Round(wf/310*pic);
  Button3.Font.Size := Round(wf/250*pic);
  Button1.Font.Size := Round(wf/250*pic);
  StaticText1.Font.Size := Round(wf/250*pic);
  Memo1.Font.Size := Round(wf/280*pic);
  Memo1.Font.Size := Round(wf/250*pic);
  Button2.Font.Size := Round(wf/250*pic);
  Label5.Font.Size := Round(wf/230*pic);
  Label4.Font.Size := Round(wf/230*pic);
  Button9.Font.Size := Round(wf/250*pic);
  Label3.Font.Size := Round(wf/310*pic);
  Label7.Font.Size := Round(wf/310*pic);
  Memo3.Font.Size := Round(wf/230*pic);
  Panel1.Font.Size := Round(wf/280*pic);
  MaskEdit1.Font.Size := Round(wf/300*pic);
  MaskEdit2.Font.Size := Round(wf/300*pic);
  Label6.Font.Size := Round(wf/310*pic);
  Label1.Font.Size := Round(wf/310*pic);
  Label3.Font.Size := Round(wf/310*pic);
  Button3.Font.Size := Round(wf/250*pic);
  Button1.Font.Size := Round(wf/250*pic);
  StaticText1.Font.Size := Round(wf/250*pic);
  Memo1.Font.Size := Round(wf/280*pic);
  Memo1.Font.Size := Round(wf/250*pic);
  Button2.Font.Size := Round(wf/250*pic);
  Label5.Font.Size := Round(wf/230*pic);
  Label4.Font.Size := Round(wf/230*pic);
  Button9.Font.Size := Round(wf/250*pic);
  Label3.Font.Size := Round(wf/310*pic);
  Label7.Font.Size := Round(wf/310*pic);



   { inivaluef := myINI.ReadFloat('Settings','Form Size', 3.0);

    if inivaluef = 2.0 then Button5.Caption := 'Size 1';
    if inivaluef = 3.0 then Button5.Caption := 'Size 2';
    if inivaluef = 4.0 then Button5.Caption := 'Size 3';
    if inivaluef = 5.0 then Button5.Caption := 'Size 4';
    if inivaluef = 1.0 then Button5.Caption := 'Size 5';   }

    myINI.Free;
    vtkout := false;
    plyout := false;
end;

procedure TForm1.ResizeEvent(Sender: TObject);
var
myINI : TINIFile;

begin
  Label5.Font.Color := clGreen;
  Timer1.enabled := false;


  button9count := button9count +1;
  savesize := savesize +1;


{ output.Add('luniverse[' + InttoStr(s) + '] ' + luniverse[s]); }
 {output.Add('ofw ' + InttoStr(ofw)); }
  if (Form1.Height < Round (0.6*Screen.Height)) AND
     (Form1.Width < Round (0.6*Screen.Width)) then
   begin
  pic := pic * 1.05;
  hh := Screen.Height;
  ww := Screen.Width;

  Form1.Height := Round(hh/2*pic);
  Form1.Width := Round(ww/2*pic);
  Memo3.Height := Round(hh/22*pic); Memo3.Width := Round(ww/2.055*pic);
  Memo3.Left := Round(ww/150*pic); Memo3.Top := Round(hh/32*pic);
  SynEdit1.Height := Round(hh/2.9*pic); SynEdit1.Width := Round(ww/2.055*pic);
  SynEdit1.Left := Round(ww/150*pic); SynEdit1.Top := Round(hh/12*pic);
  Panel1.Height := Round(hh/6*pic); Panel1.Width := Round(ww/8*pic);
  Panel1.Left := Round(hh/3.0*pic); Panel1.Top := Round(hh/15*pic);
  Button3.Height := Round(hh/40*pic); Button3.Width := Round(ww/26*pic);
  Button3.Left := Round(hh/14.5*pic); Button3.Top := Round(hh/7.7*pic);
  MaskEdit2.Height := Round(hh/40*pic); MaskEdit2.Width := Round(ww/35*pic);
  MaskEdit2.Left := Round(hh/40*pic); MaskEdit2.Top := Round(hh/14*pic);
  Label6.Height := Round(hh/30*pic); Label6.Width := Round(ww/25*pic);
  Label6.Left := Round(hh/45*pic); Label6.Top := Round(hh/10*pic);
  Label1.Height := Round(hh/30*pic); Label1.Width := Round(ww/25*pic);
  Label1.Left := Round(hh/9.5*pic); Label1.Top := Round(hh/10*pic);
  Button8.Height := Round(hh/45*pic); Button8.Width := Round(hh/45*pic);
  Button8.Left := Round(hh/6.5*pic); Button8.Top := Round(hh/14*pic);
  Button7.Height := Round(hh/45*pic); Button7.Width := Round(hh/45*pic);
  Button7.Left := Round(hh/9*pic); Button7.Top := Round(hh/14*pic);
  Button1.Height := Round(hh/45*pic); Button1.Width := Round(hh/15*pic);
  Button1.Left := Round(hh/11*pic); Button1.Top := Round(hh/4*pic);
  MaskEdit1.Height := Round(hh/40*pic); MaskEdit1.Width := Round(ww/35*pic);
  MaskEdit1.Left := Round(hh/40*pic); MaskEdit1.Top := Round(hh/50*pic);
  Label3.Height := Round(hh/30*pic); Label3.Width := Round(ww/25*pic);
  Label3.Left := Round(hh/45*pic); Label3.Top := Round(hh/22*pic);
  Panel2.Height := Round(hh/3.5*pic); Panel2.Width := Round(ww/6.5*pic);
  Panel2.Left := Round(hh/3.4*pic); Panel2.Top := Round(hh/25*pic);
  Image1.Height := Round(hh/6*pic); Image1.Width := Round(ww/5*pic);
  Image1.Left := Round(hh/25.5*pic); Image1.Top := Round(hh/55*pic);
  StaticText1.Height := Round(hh/30*pic); StaticText1.Width := Round(ww/5*pic);
  StaticText1.Left := Round(hh/20.2*pic); StaticText1.Top := Round(hh/9.5*pic);
  Memo1.Height := Round(hh/12*pic); Memo1.Width := Round(ww/5*pic);
  Memo1.Left := Round(hh/40*pic); Memo1.Top := Round(hh/6.6*pic);
  Memo2.Height := Round(hh/2.5*pic); Memo2.Width := Round(ww/2.055*pic);
  Memo2.Left := Round(ww/150*pic); Memo2.Top := Round(hh/32*pic);
  Button2.Height := Round(hh/45*pic); Button2.Width := Round(hh/8*pic);
  Button2.Left := Round(hh/2.9*pic); Button2.Top := Round(hh/2.3*pic);
  Label5.Height := Round(hh/30*pic); Label5.Width := Round(ww/2.5*pic);
  Label5.Left := Round(hh/2.5*pic); Label5.Top := Round(hh/65*pic);
  Button9.Height := Round(hh/45*pic); Button9.Width := Round(hh/45*pic);
  Button9.Left := Round(hh/7*pic); Button9.Top := Round(hh/50*pic);
  Label7.Height := Round(hh/30*pic); Label7.Width := Round(ww/2.5*pic);
  Label7.Left := Round(hh/8.6*pic); Label7.Top := Round(hh/22*pic);

  SynEdit1.Font.Size := Round(wf/230*pic);
  Memo3.Font.Size := Round(wf/230*pic);
  Panel1.Font.Size := Round(wf/280*pic);
  MaskEdit1.Font.Size := Round(wf/300*pic);
  MaskEdit2.Font.Size := Round(wf/300*pic);
  Label6.Font.Size := Round(wf/310*pic);
  Label1.Font.Size := Round(wf/310*pic);
  Label3.Font.Size := Round(wf/310*pic);
  Button3.Font.Size := Round(wf/250*pic);
  Button1.Font.Size := Round(wf/250*pic);
  StaticText1.Font.Size := Round(wf/250*pic);
  Memo1.Font.Size := Round(wf/280*pic);
  Memo1.Font.Size := Round(wf/250*pic);
  Button2.Font.Size := Round(wf/250*pic);
  Label5.Font.Size := Round(wf/230*pic);
  Label4.Font.Size := Round(wf/230*pic);
  Button9.Font.Size := Round(wf/250*pic);
  Label3.Font.Size := Round(wf/310*pic);
  Label7.Font.Size := Round(wf/310*pic);
  Memo3.Font.Size := Round(wf/230*pic);
  Panel1.Font.Size := Round(wf/280*pic);
  MaskEdit1.Font.Size := Round(wf/300*pic);
  MaskEdit2.Font.Size := Round(wf/300*pic);
  Label6.Font.Size := Round(wf/310*pic);
  Label1.Font.Size := Round(wf/310*pic);
  Label3.Font.Size := Round(wf/310*pic);
  Button3.Font.Size := Round(wf/250*pic);
  Button1.Font.Size := Round(wf/250*pic);
  StaticText1.Font.Size := Round(wf/250*pic);
  Memo1.Font.Size := Round(wf/280*pic);
  Memo1.Font.Size := Round(wf/250*pic);
  Button2.Font.Size := Round(wf/250*pic);
  Label5.Font.Size := Round(wf/230*pic);
  Label4.Font.Size := Round(wf/230*pic);
  Button9.Font.Size := Round(wf/250*pic);
  Label3.Font.Size := Round(wf/310*pic);
  Label7.Font.Size := Round(wf/310*pic);

   end
  else begin
     pic := 0.75;
  Form1.Height := Round(hh/2*pic);
  Form1.Width := Round(ww/2*pic);
  Memo3.Height := Round(hh/22*pic); Memo3.Width := Round(ww/2.055*pic);
  Memo3.Left := Round(ww/150*pic); Memo3.Top := Round(hh/32*pic);
  SynEdit1.Height := Round(hh/2.9*pic); SynEdit1.Width := Round(ww/2.055*pic);
  SynEdit1.Left := Round(ww/150*pic); SynEdit1.Top := Round(hh/12*pic);
  Panel1.Height := Round(hh/6*pic); Panel1.Width := Round(ww/8*pic);
  Panel1.Left := Round(hh/3.0*pic); Panel1.Top := Round(hh/15*pic);
  Button3.Height := Round(hh/40*pic); Button3.Width := Round(ww/26*pic);
  Button3.Left := Round(hh/14.5*pic); Button3.Top := Round(hh/7.7*pic);
  MaskEdit2.Height := Round(hh/40*pic); MaskEdit2.Width := Round(ww/35*pic);
  MaskEdit2.Left := Round(hh/40*pic); MaskEdit2.Top := Round(hh/14*pic);
  Label6.Height := Round(hh/30*pic); Label6.Width := Round(ww/25*pic);
  Label6.Left := Round(hh/45*pic); Label6.Top := Round(hh/10*pic);
  Label1.Height := Round(hh/30*pic); Label1.Width := Round(ww/25*pic);
  Label1.Left := Round(hh/9.5*pic); Label1.Top := Round(hh/10*pic);
  Button8.Height := Round(hh/45*pic); Button8.Width := Round(hh/45*pic);
  Button8.Left := Round(hh/6.5*pic); Button8.Top := Round(hh/14*pic);
  Button7.Height := Round(hh/45*pic); Button7.Width := Round(hh/45*pic);
  Button7.Left := Round(hh/9*pic); Button7.Top := Round(hh/14*pic);
  Button1.Height := Round(hh/45*pic); Button1.Width := Round(hh/15*pic);
  Button1.Left := Round(hh/11*pic); Button1.Top := Round(hh/4*pic);
  MaskEdit1.Height := Round(hh/40*pic); MaskEdit1.Width := Round(ww/35*pic);
  MaskEdit1.Left := Round(hh/40*pic); MaskEdit1.Top := Round(hh/50*pic);
  Label3.Height := Round(hh/30*pic); Label3.Width := Round(ww/25*pic);
  Label3.Left := Round(hh/45*pic); Label3.Top := Round(hh/22*pic);
  Panel2.Height := Round(hh/3.5*pic); Panel2.Width := Round(ww/6.5*pic);
  Panel2.Left := Round(hh/3.4*pic); Panel2.Top := Round(hh/25*pic);
  Image1.Height := Round(hh/6*pic); Image1.Width := Round(ww/5*pic);
  Image1.Left := Round(hh/25.5*pic); Image1.Top := Round(hh/55*pic);
  StaticText1.Height := Round(hh/30*pic); StaticText1.Width := Round(ww/5*pic);
  StaticText1.Left := Round(hh/20.2*pic); StaticText1.Top := Round(hh/9.5*pic);
  Memo1.Height := Round(hh/12*pic); Memo1.Width := Round(ww/5*pic);
  Memo1.Left := Round(hh/40*pic); Memo1.Top := Round(hh/6.6*pic);
  Memo2.Height := Round(hh/2.5*pic); Memo2.Width := Round(ww/2.055*pic);
  Memo2.Left := Round(ww/150*pic); Memo2.Top := Round(hh/32*pic);
  Button2.Height := Round(hh/45*pic); Button2.Width := Round(hh/8*pic);
  Button2.Left := Round(hh/2.9*pic); Button2.Top := Round(hh/2.3*pic);
  Label5.Height := Round(hh/30*pic); Label5.Width := Round(ww/2.5*pic);
  Label5.Left := Round(hh/2.5*pic); Label5.Top := Round(hh/65*pic);
  Button9.Height := Round(hh/45*pic); Button9.Width := Round(hh/45*pic);
  Button9.Left := Round(hh/7*pic); Button9.Top := Round(hh/50*pic);
  Label7.Height := Round(hh/30*pic); Label7.Width := Round(ww/2.5*pic);
  Label7.Left := Round(hh/8.6*pic); Label7.Top := Round(hh/22*pic);

  SynEdit1.Font.Size := Round(wf/230*pic);
  Memo3.Font.Size := Round(wf/230*pic);
  Panel1.Font.Size := Round(wf/280*pic);
  MaskEdit1.Font.Size := Round(wf/300*pic);
  MaskEdit2.Font.Size := Round(wf/300*pic);
  Label6.Font.Size := Round(wf/310*pic);
  Label1.Font.Size := Round(wf/310*pic);
  Label3.Font.Size := Round(wf/310*pic);
  Button3.Font.Size := Round(wf/250*pic);
  Button1.Font.Size := Round(wf/250*pic);
  StaticText1.Font.Size := Round(wf/250*pic);
  Memo1.Font.Size := Round(wf/280*pic);
  Memo1.Font.Size := Round(wf/250*pic);
  Button2.Font.Size := Round(wf/250*pic);
  Label5.Font.Size := Round(wf/230*pic);
  Label4.Font.Size := Round(wf/230*pic);
  Button9.Font.Size := Round(wf/250*pic);
  Label3.Font.Size := Round(wf/310*pic);
  Label7.Font.Size := Round(wf/310*pic);
  Memo3.Font.Size := Round(wf/230*pic);
  Panel1.Font.Size := Round(wf/280*pic);
  MaskEdit1.Font.Size := Round(wf/300*pic);
  MaskEdit2.Font.Size := Round(wf/300*pic);
  Label6.Font.Size := Round(wf/310*pic);
  Label1.Font.Size := Round(wf/310*pic);
  Label3.Font.Size := Round(wf/310*pic);
  Button3.Font.Size := Round(wf/250*pic);
  Button1.Font.Size := Round(wf/250*pic);
  StaticText1.Font.Size := Round(wf/250*pic);
  Memo1.Font.Size := Round(wf/280*pic);
  Memo1.Font.Size := Round(wf/250*pic);
  Button2.Font.Size := Round(wf/250*pic);
  Label5.Font.Size := Round(wf/230*pic);
  Label4.Font.Size := Round(wf/230*pic);
  Button9.Font.Size := Round(wf/250*pic);
  Label3.Font.Size := Round(wf/310*pic);
  Label7.Font.Size := Round(wf/310*pic);


  end;

 { *  myINI := TINIFile.Create(ExtractFilePath(Application.EXEName) +
  'blenbridge.ini');  * }

   { inivaluef := myINI.ReadFloat('Settings','Form Size', 3.0);

    if inivaluef = 2.0 then Button5.Caption := 'Size 1';
    if inivaluef = 3.0 then Button5.Caption := 'Size 2';
    if inivaluef = 4.0 then Button5.Caption := 'Size 3';
    if inivaluef = 5.0 then Button5.Caption := 'Size 4';
    if inivaluef = 1.0 then Button5.Caption := 'Size 5';   }

  { *  myINI.Free; * }
    vtkout := false;
    plyout := false;

end;

procedure TForm1.MenuItem10Click(Sender: TObject);
begin
  Panel1.Visible := true;
end;

procedure TForm1.MenuItem11Click(Sender: TObject);
begin
  Panel1.Visible := true;
end;

procedure TForm1.MenuItem12Click(Sender: TObject);
begin
  Panel1.Visible := true;
end;

procedure TForm1.MenuItem13Click(Sender: TObject);
begin
  Panel1.Visible := true;
end;

procedure TForm1.MenuItem14Click(Sender: TObject);
begin
  Panel1.Visible := true;
end;

procedure TForm1.MenuItem15Click(Sender: TObject);
begin

end;

procedure TForm1.MenuItem16Click(Sender: TObject);
begin
  {  Label7MouseDown(Sender: TObject; Button: TMouseButton; Shift:
  TShiftState; X, Y: Integer);}
  OpenURL('https://blenbridge.sourceforge.io/');
end;

procedure TForm1.MenuItem17Click(Sender: TObject);
begin
  Panel2.Visible := true;
end;

procedure TForm1.MenuItem18Click(Sender: TObject);
begin
  Memo2.Visible := true;
  Button2.Visible := true;
end;

procedure TForm1.MenuItem4Click(Sender: TObject);
begin
   Label5.visible := false;
 if opendialog1.execute then
    begin
    myvar3:= opendialog1.filename;
    SynEdit1.lines.LoadFromFile(myvar3);
    end;

    Memo3.Lines.Add(myvar3);
end;

procedure TForm1.MenuItem5Click(Sender: TObject);
begin

   if vtkout = true then begin
   outfilename := AnsiReplaceStr(myvar3, 'ply', 'vtk');
   end
   else if plyout = true then begin
   outfilename := AnsiReplaceStr(myvar3, 'vtk', 'ply');
   end
   else outfilename := myvar3;
   Label5.visible := false;
   {savedialog1.FileName := myvar3; }
   savedialog1.FileName := outfilename;
   if savedialog1.execute then
    begin
    myvar4 := savedialog1.filename;
    output.SaveToFile(myvar4);
  end;

   plyout := false;
   vtkout := false;
end;

procedure TForm1.MenuItem6Click(Sender: TObject);
begin
   FormDestroy(Sender);
end;

procedure TForm1.MenuItem7Click(Sender: TObject);
begin
   if myvar3 <> '' then begin
   Label5.visible := true;
   Label5.Caption := 'Initializing ' ;
   Application.ProcessMessages;
   PlyWriteVtk(Sender);
   end;
end;

procedure TForm1.MenuItem8Click(Sender: TObject);
begin
   if myvar3 <> '' then
  Label5.visible := true;
  Application.ProcessMessages;
  VtkWritePly(Sender);
end;

procedure TForm1.MenuItem9Click(Sender: TObject);
begin
 {No action required for this event;  merely setting the checkbox is
 all that is required.
 Because the check mark accompanying this item is so small, I decided to put
 the following text notification in also. I tested it and found that, just
 as desired, checking followed by unchecking (before execution) results in NO
 field data being  written.}

  if MenuItem9.Caption = 'Include field data' then
   MenuItem9.Caption := 'Field data will be included'
   else if
   MenuItem9.Caption = 'Field data will be included' then
   MenuItem9.Caption := 'Include field data';

end;

procedure TForm1.Timer1StartTimer(Sender: TObject);
begin
  // Timer1.Enabled := true;
end;

procedure TForm1.Timer1StopTimer(Sender: TObject);
begin
  Timer1.Enabled := false;
end;

procedure TForm1.Timer1Timer(Sender: TObject);
begin
  ElapsedT := ElapsedT + 1;
  if ElapsedT >= 3600 then
  Label4.Caption := InttoStr(Trunc(ElapsedT / 3600)) + ' hours ' +
    InttoStr(Trunc(ElapsedT / 60) Mod 60) + ' minutes '
    + InttoStr(ElapsedT Mod 60) +  ' seconds elapsed'

    else
  if (ElapsedT >= 60) AND (ElapsedT < 3600) then
  //Label2.Caption := Format('%f', [ElapsedT / 60]) + ' minutes elapsed'  ;
  Label4.Caption := InttoStr(Trunc(ElapsedT / 60)) + ' minutes ' +
    InttoStr(ElapsedT Mod 60) +  ' seconds elapsed'

  else
  if ElapsedT < 60 then
  {Label2.Caption := Format('%f', [ElapsedT]) + ' seconds elapsed';  }
  Label4.Caption := FloattoStr(ElapsedT) + ' seconds elapsed';
  //Application.ProcessMessages;


  Timer1StartTimer(Sender);

end;

procedure TForm1.PlyWriteVtk(Sender: TObject);
var
   i : Integer;
   tempStr : String;

begin
   Timer1.Enabled := true;
   ElapsedT := 0;
   Timer1StartTimer(Sender);

   eightblobsf := TStringlist.Create; {list of blobs of all elements}
   eightblobsf.Sorted := false;
   eightblobsf.Duplicates := dupAccept;
   eightblobsf.Clear;
   xside := TStringlist.Create;   {cell max x length in cell order}
   xside.Sorted := false;
   xside.Duplicates := dupIgnore;
   xside.Clear;
   yside := TStringlist.Create;   {cell max y length in cell order}
   yside.Sorted := false;
   yside.Duplicates := dupIgnore;
   yside.Clear;
   zside := TStringlist.Create;   {cell max z length in cell order}
   zside.Sorted := false;
   zside.Duplicates := dupIgnore;
   zside.Clear;
   sidecume := TStringlist.Create;  {cell side dimensions, one cell per card.}
   sidecume.Sorted := false;
   sidecume.Duplicates := dupIgnore;
   sidecume.Clear;
   vertlistf := TStringlist.Create;  {vert sequence for each face, 1 face per card }
   vertlistf.Sorted := false;
   vertlistf.Duplicates := dupIgnore;
   vertlistf.Clear;
   hopper1 := TStringlist.Create;  {vert blobs of intermediate faces are sorted }
   hopper1.Sorted := true;
   hopper1.Duplicates := dupIgnore;
   hopper1.Clear;
   wooda := TStringlist.Create;  { faces lists are sorted and reduced in number}
   wooda.Sorted := true;
   wooda.Duplicates := dupIgnore;
   wooda.Clear;
   Trigarray := TStringlist.Create;  {share edge with primary working face}
   Trigarray.Sorted := false;
   Trigarray.Duplicates := dupIgnore;
   Trigarray.Clear;
   Trigarray2 := TStringlist.Create;  {share edge with secondary unconfirmed edge}
   Trigarray2.Sorted := false;
   Trigarray2.Duplicates := dupIgnore;
   Trigarray2.Clear;
   finalindex := TStringlist.Create;  {double index reference to eightblobs}
   finalindex.Sorted := false;
   finalindex.Duplicates := dupAccept;
   finalindex.Clear;
   blobsworth := TStringlist.Create;  {the final vert list but not in vtk order}
   blobsworth.Sorted := false;
   blobsworth.Duplicates := dupIgnore;
   blobsworth.Clear;
   luniverse := TStringlist.Create; {reduced set of faces within a distance }
   luniverse.Sorted := false;
   luniverse.Duplicates := dupIgnore;
   luniverse.Clear;
   output := TStringlist.Create; {holds text for output }
   output.Sorted := false;
   output.Duplicates := dupIgnore;
   output.Clear;
   oneedge := TStringlist.Create; {holds text for output }
   oneedge.Sorted := false;
   oneedge.Duplicates := dupIgnore;
   oneedge.Clear;
   twoedge := TStringlist.Create; {holds text for output }
   twoedge.Sorted := false;
   twoedge.Duplicates := dupIgnore;
   twoedge.Clear;
   eightblobs3 := TStringlist.Create; {holds text for output }
   eightblobs3.Sorted := false;
   eightblobs3.Duplicates := dupIgnore;
   eightblobs3.Clear;

   F := 1;

   output.Add('# vtk DataFile Version 3.0');
   output.Add('# created by Blenbridge 1.21');
   output.Add('ASCII');
   output.Add('DATASET UNSTRUCTURED_GRID');

   {Get the number of verts}
   REPEAT
   tempStr := trim(SynEdit1.Lines[F]);
   if AnsiPos('vertex', tempStr) = 0 then
   F := F + 1;
   until AnsiPos('vertex', tempStr) <> 0;

   numberofverts := StrtoInt(GetToken(tempStr, ' ', 3));

   {Get the number of faces.}

   REPEAT
   tempStr := trim(SynEdit1.Lines[F]);
   if AnsiPos('face', tempStr) = 0 then
   F := F + 1;
   until (AnsiPos('face', tempStr) <> 0) OR (F = SynEdit1.Lines.Count);

   numberoffaces := StrtoInt(GetToken(tempStr, ' ', 3));

   {Capture the coords of the verts as floats in 3 arrays and as
   strings in stringlist vertlistf.  Print them out.}

   F := F +3;
   i := 0;

   output.Add('POINTS ' + InttoStr(numberofverts) + ' float');

   REPEAT
   tempStr := trim(SynEdit1.Lines[F]);

   output.Add(tempStr);

   Numarrayx[i] := StrtoFloat(GetToken(tempStr, ' ', 1));
   Numarrayy[i] := StrtoFloat(GetToken(tempStr, ' ', 2));
   Numarrayz[i] := StrtoFloat(GetToken(tempStr, ' ', 3));
   F := F +1;
   i := i +1;
   until i = numberofverts ;

   {Find out whether the .ply file stores tets or hexes. If tets, go to the
   appropriate procedure }
   tempStr := trim(SynEdit1.Lines[F]);

   if GetToken(tempStr, ' ', 1) = '3' then begin
   Ply3WriteVTK(Sender);
   end
   else begin
      Ply4WriteVTK(Sender);
   end;
   end;

  procedure TForm1.Ply4WriteVtk(Sender: TObject);
  var
     vec1, vec2, vec3, maxvec : Double;
     tempStr : String;
     i : Integer;
  begin

   {Capture the string blobs which represent the connectivity of each face.
   These will be used later for constructing elements.}

   REPEAT
   tempStr := trim(SynEdit1.Lines[F]);
   vertlistf.Add(' ' + GetToken(tempStr, ' ', 2) + ' ' +
   GetToken(tempStr, ' ', 3) + ' ' +
   GetToken(tempStr, ' ', 4) + ' ' +
   GetToken(tempStr, ' ', 5) + ' ');
   F := F + 1;
   until F = SynEdit1.Lines.Count {numberoffaces -i -2};

   {Fill 3 arrays centroid-x,-y,-z of doubles with the coordinates of the
   centroids of all the faces. Find the largest intra-face point-to-point
   distance, maxvec, for each face and store in the array longvec. A
   mini-universe of face candidates will be created in the stringlist luniverse.
   To get in, for the working [i] face the centroid-to-centroid distance with the
   candidate must be less than radfac times the sum of the two maxvecs. This
   cuts down the searching greatly.}

   for i := 0 to vertlistf.Count -1 do begin
   centroidx[i] := 0.25 * (Numarrayx[StrtoInt(GetToken(vertlistf[i], ' ', 2))] +
   Numarrayx[StrtoInt(GetToken(vertlistf[i], ' ', 3))] +
   Numarrayx[StrtoInt(GetToken(vertlistf[i], ' ', 4))] +
   Numarrayx[StrtoInt(GetToken(vertlistf[i], ' ', 5))] );
   centroidy[i] := 0.25 * (Numarrayy[StrtoInt(GetToken(vertlistf[i], ' ', 2))] +
   Numarrayy[StrtoInt(GetToken(vertlistf[i], ' ', 3))] +
   Numarrayy[StrtoInt(GetToken(vertlistf[i], ' ', 4))] +
   Numarrayy[StrtoInt(GetToken(vertlistf[i], ' ', 5))] );
   centroidz[i] := 0.25 * (Numarrayz[StrtoInt(GetToken(vertlistf[i], ' ', 2))] +
   Numarrayz[StrtoInt(GetToken(vertlistf[i], ' ', 3))] +
   Numarrayz[StrtoInt(GetToken(vertlistf[i], ' ', 4))] +
   Numarrayz[StrtoInt(GetToken(vertlistf[i], ' ', 5))] );

   vec1 := Sqrt((Numarrayx[StrtoInt(GetToken(vertlistf[i], ' ', 2))] -
   Numarrayx[StrtoInt(GetToken(vertlistf[i], ' ', 3))]) *
   (Numarrayx[StrtoInt(GetToken(vertlistf[i], ' ', 2))] -
   Numarrayx[StrtoInt(GetToken(vertlistf[i], ' ', 3))])   +
   (Numarrayy[StrtoInt(GetToken(vertlistf[i], ' ', 2))] -
   Numarrayy[StrtoInt(GetToken(vertlistf[i], ' ', 3))]) *
   (Numarrayy[StrtoInt(GetToken(vertlistf[i], ' ', 2))] -
   Numarrayy[StrtoInt(GetToken(vertlistf[i], ' ', 3))])   +
   (Numarrayz[StrtoInt(GetToken(vertlistf[i], ' ', 2))] -
   Numarrayz[StrtoInt(GetToken(vertlistf[i], ' ', 3))]) *
   (Numarrayz[StrtoInt(GetToken(vertlistf[i], ' ', 2))] -
   Numarrayz[StrtoInt(GetToken(vertlistf[i], ' ', 3))])   );

   vec2 := Sqrt((Numarrayx[StrtoInt(GetToken(vertlistf[i], ' ', 2))] -
   Numarrayx[StrtoInt(GetToken(vertlistf[i], ' ', 4))]) *
   (Numarrayx[StrtoInt(GetToken(vertlistf[i], ' ', 2))] -
   Numarrayx[StrtoInt(GetToken(vertlistf[i], ' ', 4))])   +
   (Numarrayy[StrtoInt(GetToken(vertlistf[i], ' ', 2))] -
   Numarrayy[StrtoInt(GetToken(vertlistf[i], ' ', 4))]) *
   (Numarrayy[StrtoInt(GetToken(vertlistf[i], ' ', 2))] -
   Numarrayy[StrtoInt(GetToken(vertlistf[i], ' ', 4))])   +
   (Numarrayz[StrtoInt(GetToken(vertlistf[i], ' ', 2))] -
   Numarrayz[StrtoInt(GetToken(vertlistf[i], ' ', 4))]) *
   (Numarrayz[StrtoInt(GetToken(vertlistf[i], ' ', 2))] -
   Numarrayz[StrtoInt(GetToken(vertlistf[i], ' ', 4))])   );

   vec3 := Sqrt((Numarrayx[StrtoInt(GetToken(vertlistf[i], ' ', 2))] -
   Numarrayx[StrtoInt(GetToken(vertlistf[i], ' ', 5))]) *
   (Numarrayx[StrtoInt(GetToken(vertlistf[i], ' ', 2))] -
   Numarrayx[StrtoInt(GetToken(vertlistf[i], ' ', 5))])   +
   (Numarrayy[StrtoInt(GetToken(vertlistf[i], ' ', 2))] -
   Numarrayy[StrtoInt(GetToken(vertlistf[i], ' ', 5))]) *
   (Numarrayy[StrtoInt(GetToken(vertlistf[i], ' ', 2))] -
   Numarrayy[StrtoInt(GetToken(vertlistf[i], ' ', 5))])   +
   (Numarrayz[StrtoInt(GetToken(vertlistf[i], ' ', 2))] -
   Numarrayz[StrtoInt(GetToken(vertlistf[i], ' ', 5))]) *
   (Numarrayz[StrtoInt(GetToken(vertlistf[i], ' ', 2))] -
   Numarrayz[StrtoInt(GetToken(vertlistf[i], ' ', 5))])   );

   maxvec := vec1;
   if (vec1 > vec2) AND (vec1 > vec3) then maxvec := vec1
   else if (vec2 > vec1) AND (vec2 > vec3) then maxvec := vec2
   else if (vec3 > vec1) AND (vec3 > vec2) then maxvec := vec3;

   longvec[i] := maxvec;
   end;

   SearchforEdge(Sender);

end;


procedure TForm1.SearchforEdge(Sender: TObject);
var  i, n, s, e : Integer;
  { charz,} a1, a2, a3, a4, FES, flst, flsb, topkey, bottomkey : String;
   cop1x, cop1y, cop1z, cop2x, cop2y, cop2z, cop3x, cop3y, cop3z, coph, copw,
   copl, copvol, copcpx, copcpy, copcpz, comvol, coppa : Double;
   writeit : Boolean;

begin

   radfac := StrtoInt(MaskEdit1.Text);
   comvol := StrtoFloat(MaskEdit2.Text);
   {====================================================================}
      {The i loop presents each face sequentially, and all reasonable
      hex elements are constructed from it and around it. About 80 - 90
      percent of these are later deleted through sorting stringlists.}

      for i := 0 to vertlistf.Count -1 do begin

       Label5.Caption := 'Working on face ' + InttoStr(i +1) + ' of ' +
       InttoStr(numberoffaces);
       Application.ProcessMessages;

      luniverse.Clear;
      Trigarray.Clear;

      a1 := GetToken(vertlistf[i], ' ', 2);
      a2 := GetToken(vertlistf[i], ' ', 3);
      a3 := GetToken(vertlistf[i], ' ', 4);
      a4 := GetToken(vertlistf[i], ' ', 5);

      {The luniverse stringlist is populated. Using a factor of 'radfac' to decide
      whether to include faces will miss elements with aspect ratio greater than that,
      which could be a considerable number, but the savings in time makes it
      worth it.}

      for e := 0 to vertlistf.Count -1 do begin
      if e <> i then
      if Sqrt((centroidx[i] - centroidx[e]) * (centroidx[i] - centroidx[e]) +
      (centroidy[i] - centroidy[e]) * (centroidy[i] - centroidy[e]) +
      (centroidz[i] - centroidz[e]) * (centroidz[i] - centroidz[e]) )  <
      radfac * (longvec[i] + longvec[e]) then luniverse.Add(vertlistf[e]);
      end;

      {The sections marked with 'chk' are diagnostic. They result in output that
      can be analyzed to see what lines are causing errors with various actions
      that are performed.}

      {chk
      for s := 0 to luniverse.Count -1 do
      output.Add('luniverse[' + InttoStr(s) + '] ' + luniverse[s]);
      chk}

      {====================================================================}
      {Make collections of the faces that share an edge with a1-a2.
      They go into stringlist Trigarray.}

      {chk
      output.Add('vertlistf.count ' + InttoStr(vertlistf.count));
      output.Add('vertlistf[' + InttoStr(i) + '] ' + vertlistf[i]);
      output.Add('r = 1');
      output.Add('a1= ' + a1 + ' a2= ' + a2);
      output.Add('numberoffaces ' + InttoStr(numberoffaces));
      chk}

      for n := 0 to luniverse.Count -1 do begin
      if (AnsiPos(' ' + a1 + ' ', luniverse[n]) <> 0) then
      if (AnsiPos(' ' + a2 + ' ', luniverse[n]) <> 0) then
      if luniverse[n] <> vertlistf[i] then begin
      Trigarray.Add(luniverse[n]);
      end;
      end;

     { chk
      output.Add( ' ');
      output.Add('vertlistf[' + InttoStr(i) + '] .' + vertlistf[i] + '.');
      for s := 0 to Trigarray.Count -1 do
      output.Add('Trigarray[' + InttoStr(s) + '] .' + Trigarray[s] + '.');
      output.Add('a1= .' + a1 + '. a2= .' + a2 + '.');
      output.Add('a3= .' + a3 + '. a4= .' + a4 + '.');
      chk  }

      for s := 0 to Trigarray.Count -1 do begin
      writeit := false;
      flst := '';
      flsb := '';
      coppa := 0.0;
      copvol := 0.0;

      {*********************************************}
      {It is necessary (for vtk winding) to know which points in prospective
      faces share an edge with a1 and a2 and exactly which edge they share.
      In about three assignment situations, there are twelve possibilities,
      which the function FindEdgeSite interrogates by boring brute force.}

      FES := FindEdgeSite(a1, a2, GetToken(Trigarray[s], ' ', 2),
      GetToken(Trigarray[s], ' ', 3), GetToken(Trigarray[s], ' ', 4),
      GetToken(Trigarray[s], ' ', 5));

      a1adj := GetToken(FES, ',', 1);
      a2adj := GetToken(FES, ',', 2);

 {=\/=\/=\/=\/=\/=\/=\/=\/=\/=\/=\/=\/=\/=\/=\/=\/=\/=\/=\/=\/=\/=\/=\/=\/=\/=}

      cop3x :=  Numarrayx[StrtoInt(a1) ] -Numarrayx[StrtoInt(a4) ];
      cop3y :=  Numarrayy[StrtoInt(a1) ] -Numarrayy[StrtoInt(a4) ];
      cop3z :=  Numarrayz[StrtoInt(a1) ] -Numarrayz[StrtoInt(a4) ];
      cop2x :=  Numarrayx[StrtoInt(a1) ] -Numarrayx[StrtoInt(a2) ];
      cop2y :=  Numarrayy[StrtoInt(a1) ] -Numarrayy[StrtoInt(a2) ];
      cop2z :=  Numarrayz[StrtoInt(a1) ] -Numarrayz[StrtoInt(a2) ];
      cop1x :=  Numarrayx[StrtoInt(a1) ] -Numarrayx[StrtoInt(a1adj) ];
      cop1y :=  Numarrayy[StrtoInt(a1) ] -Numarrayy[StrtoInt(a1adj) ];
      cop1z :=  Numarrayz[StrtoInt(a1) ] -Numarrayz[StrtoInt(a1adj) ];

      {A safeguard against bad adjacent face choice is to look at a1,
      a2, a4 and a1adj to make sure they are not coplanar. A minimum value
      for their tet volume will be set in coppa.}

      {I decided to scrap the separate functions for dot product and cross
      product, since they are only used right here. For reference,
      ============================================================
      cross product AxB = (a2b3 - a3b2, a3b1 - a1b3, a1b2 - a2b1)
      dot product AxB = (a1*b1 + a2*b2 + a3*b3)
      ============================================================
      As the dot product of a cross product, comvol is actually a triple
      product.}

      copcpx := (cop3y*cop2z) -(cop3z*cop2y);
      copcpy := (cop3z*cop2x) -(cop3x*cop2z);
      copcpz := (cop3x*cop2y) -(cop3y*cop2x);

      coppa := (cop1x * copcpx) + (cop1y * copcpy) + (cop1z * copcpz);

      if IsNan(coppa) = true then coppa := 0.0;
      coph :=  Sqrt(cop1x*cop1x + cop1y*cop1y +cop1z*cop1z);
      copw :=  Sqrt(cop2x*cop2x + cop2y*cop2y +cop2z*cop2z);
      copl :=  Sqrt(cop3x*cop3x + cop3y*cop3y +cop3z*cop3z);
      copvol := coph * copw * copl;

      {chk
      output.Add('coppa ' + FloattoStr(coppa));
      output.Add('Abs(coppa) ' + FloattoStr(Abs(coppa)));
      output.Add('copvol ' + FloattoStr(copvol));
      chk}

      {Since septemp holds Doubles, I could use the 'AND' logic structure,
      which I can't do for Strings.  However, I'm used to the clunky
      'if .. then if .. then' way now.}

      for e := 0 to luniverse.Count -1 do begin
      if (AnsiPos(' ' + a1adj + ' ', luniverse[e]) <> 0) then
      if (AnsiPos(' ' + a1 + ' ', luniverse[e]) <> 0) then
      if (AnsiPos(' ' + a4 + ' ', luniverse[e]) <> 0) then
      flst := luniverse[e];
      end;

      for e := 0 to luniverse.Count -1 do begin
      if (AnsiPos(' ' + a2adj + ' ', luniverse[e]) <> 0) then
      if (AnsiPos(' ' + a2 + ' ', luniverse[e]) <> 0) then
      if (AnsiPos(' ' + a3 + ' ', luniverse[e]) <> 0) then
      flsb := luniverse[e];
      end;

      topkey := '';
      if flst <> '' then begin
      begin
      if GetToken(flst, ' ', 2) <> a1adj then
      if GetToken(flst, ' ', 2) <> a1 then
      if GetToken(flst, ' ', 2) <> a4 then
      if GetToken(flst, ' ', 2) <> a2adj then
      if GetToken(flst, ' ', 2) <> a2 then
      if GetToken(flst, ' ', 2) <> a3 then
      topkey := GetToken(flst, ' ', 2)
      end;
      begin
      if GetToken(flst, ' ', 3) <> a1adj then
      if GetToken(flst, ' ', 3) <> a1 then
      if GetToken(flst, ' ', 3) <> a4 then
      if GetToken(flst, ' ', 3) <> a2adj then
      if GetToken(flst, ' ', 3) <> a2 then
      if GetToken(flst, ' ', 3) <> a3 then
      topkey := GetToken(flst, ' ', 3)
      end;
      begin
      if GetToken(flst, ' ', 4) <> a1adj then
      if GetToken(flst, ' ', 4) <> a1 then
      if GetToken(flst, ' ', 4) <> a4 then
      if GetToken(flst, ' ', 4) <> a2adj then
      if GetToken(flst, ' ', 4) <> a2 then
      if GetToken(flst, ' ', 4) <> a3 then
      topkey := GetToken(flst, ' ', 4)
      end;
      begin
      if GetToken(flst, ' ', 5) <> a1adj then
      if GetToken(flst, ' ', 5) <> a1 then
      if GetToken(flst, ' ', 5) <> a4 then
      if GetToken(flst, ' ', 5) <> a2adj then
      if GetToken(flst, ' ', 5) <> a2 then
      if GetToken(flst, ' ', 5) <> a3 then
      topkey := GetToken(flst, ' ', 5)
      end;
      end
      else topkey := '';

      bottomkey := '';
      if flsb <> '' then begin
      begin
      if GetToken(flsb, ' ', 2) <> a1 then
      if GetToken(flsb, ' ', 2) <> a4 then
      if GetToken(flsb, ' ', 2) <> a1adj then
      if GetToken(flsb, ' ', 2) <> a2adj then
      if GetToken(flsb, ' ', 2) <> a2 then
      if GetToken(flsb, ' ', 2) <> a3 then
      bottomkey := GetToken(flsb, ' ', 2)
      end;
      begin
      if GetToken(flsb, ' ', 3) <> a1 then
      if GetToken(flsb, ' ', 3) <> a4 then
      if GetToken(flsb, ' ', 3) <> a1adj then
      if GetToken(flsb, ' ', 3) <> a2adj then
      if GetToken(flsb, ' ', 3) <> a2 then
      if GetToken(flsb, ' ', 3) <> a3 then
      bottomkey := GetToken(flsb, ' ', 3)
      end;
      begin
      if GetToken(flsb, ' ', 4) <> a1 then
      if GetToken(flsb, ' ', 4) <> a4 then
      if GetToken(flsb, ' ', 4) <> a1adj then
      if GetToken(flsb, ' ', 4) <> a2adj then
      if GetToken(flsb, ' ', 4) <> a2 then
      if GetToken(flsb, ' ', 4) <> a3 then
      bottomkey := GetToken(flsb, ' ', 4)
      end;
      begin
      if GetToken(flsb, ' ', 5) <> a1 then
      if GetToken(flsb, ' ', 5) <> a4 then
      if GetToken(flsb, ' ', 5) <> a1adj then
      if GetToken(flsb, ' ', 5) <> a2adj then
      if GetToken(flsb, ' ', 5) <> a2 then
      if GetToken(flsb, ' ', 5) <> a3 then
      bottomkey := GetToken(flsb, ' ', 5)
      end;
      end
      else bottomkey := '';

     { chk
      output.Add( 'a1adj a1 a4 = '  + a1adj + ' ' + a1 + ' ' + a4);
      output.Add( 'a2adj a2 a3 = '  + a2adj + ' ' + a2 + ' ' + a3);
      output.Add('flst = .' + flst + '.');
      output.Add('flsb = .' + flsb + '.');
      output.Add('topkey bottomkey .' + topkey + '. .' + bottomkey + '.');
      chk }

      {The block below double-checks to make sure the prospective keystone
      face is present in luniverse. This particular check may greatly simplify
      identification of the opposite face. Note: both coppa and copvol represent
      volumes, but a reasonable relation factor to use is a guess and subject
      to change.}

      for e := 0 to luniverse.Count -1 do begin
      if (AnsiPos(' ' + a1adj + ' ', luniverse[e]) <> 0) then
     { if (AnsiPos(' ' + a1 + ' ', luniverse[e]) <> 0) then
      if (AnsiPos(' ' + a4 + ' ', luniverse[e]) <> 0) then }
      if (AnsiPos(' ' + a2adj + ' ', luniverse[e]) <> 0) then
      if (AnsiPos(' ' + topkey + ' ', luniverse[e]) <> 0) then
      if (AnsiPos(' ' + bottomkey + ' ', luniverse[e]) <> 0) then
      begin
     { if Abs(coppa) > comvol * copvol then begin}
      {chk
      output.Add('luniverse[e] ' + luniverse[e]);
      chk}
      writeit := true;
      end;
      end;

      if writeit = true then begin
      if a1 <> '' then
      if a2 <> '' then
      if a3 <> '' then
      if a4 <> '' then
      if a1adj <> '' then
      if a2adj <> '' then
      if topkey <> '' then
      if bottomkey <> '' then
      begin
      Trigarray2.Add(' ' + a1 + ' ' + a2 + ' ' + a3 +  ' ' + a4 + ' '
      + a1adj + ' ' +  a2adj + ' '  + bottomkey + ' '  + topkey + ' ');

     { tempT2 := '.' + a1 + ' ' + a2 + ' ' + a3 +  ' ' + a4 + ' '
      + a1adj + ' ' +  a2adj + ' '  + bottomkey + ' '  + topkey + '.';  }
      end;

      {chk
      output.Add('tempT2' + tempT2);
      output.Add('Trigarray2.Count ' + InttoStr(Trigarray2.Count));
      chk}

      end;    {if writeit = true then begin}

      end; {for s := 0 to Trigarray.Count -1 do begin }

      for e := 0 to Trigarray2.Count -1 do begin
      eightblobs[e] := Trim(Trigarray2[e]);

      end;

      end;  { for i := 0 to numberoffaces -1 do begin }


     { EnforceVerdictWinding(Sender); }

      {All the data have been generated at this point, and the i
      loop ends.}

      {chk
      for s := 0 to Trigarray2.Count -1 do
      output.Add('eightblobs[' + InttoStr(s) + '] ' + eightblobs[s]);
      chk}

       ProcessEightBlobs(Sender);
end;

procedure TForm1.ProcessEightBlobs(Sender: TObject);
var
   e, s, j, m : Integer;
   gofur : Boolean;
   tib1, tib2, tib3, tib4, tib5, tia5, tia1, tia2, tia3, tia4,
   le1, le2, sind, charz : String;
begin
   {===============================================}
      {Two consecutive sorted stringlists come next. This
      might be a little tricky for Lazarus. }
      {Lazarus stringlists do not sort correctly, putting the number
      11 before the number 4, for example.  However, it is not
      necessary that the sorting be done correctly, only that it
      be done consistently, allowing the elimination of duplicates.}

        for e := 0 to Trigarray2.Count -1 do begin
        if eightblobs[e] <> '' then
        eightblobs[e] := eightblobs[e] + ' z' + InttoStr(e);
        end;

        wooda.Clear;
        try

        for s := 0 to Trigarray2.Count -1 do begin

        hopper1.Clear;

        hopper1.Add(GetToken(eightblobs[s], ' ', 1));
        hopper1.Add(GetToken(eightblobs[s], ' ', 2));
        hopper1.add(GetToken(eightblobs[s], ' ', 3));
        hopper1.add(GetToken(eightblobs[s], ' ', 4));
        hopper1.add(GetToken(eightblobs[s], ' ', 5));
        hopper1.add(GetToken(eightblobs[s], ' ', 6));
        hopper1.add(GetToken(eightblobs[s], ' ', 7));
        hopper1.add(GetToken(eightblobs[s], ' ', 8));
        hopper1.add(GetToken(eightblobs[s], ' ', 9));

        wooda.Add(hopper1[0] + ' ' +
        hopper1[1] + ' ' +
        hopper1[2] + ' ' +
        hopper1[3] + ' ' +
        hopper1[4] + ' ' +
        hopper1[5] + ' ' +
        hopper1[6] + ' ' +
        hopper1[7]  + ' ' +
        hopper1[8]
        );
        end;

        {If the below message is shown, it means the vtk output will be
        flawed. One quick trick which might work is to import the .ply
        file into Blender and then export it again. This round-trip sometimes
        helps, for some reason.
        The specific check described in the help message below actually
        worked for me. But I installed some more safeguards, and it should
        no longer show up.}

        except
           on e: EStringListError do begin
           MyShowMessage('Exception thrown here may' + #10 +
           ' mean duplicate vertices in the input.' + #10 +
           ' Save output and look around Trigarray2['
           + InttoStr(s +1) + '] for a duplicated point.', ['']);
           for m := 0 to Trigarray2.Count -1 do
           output.Add('Trigarray2[' + InttoStr(m) + '] ' + Trigarray2[m]);
         end;
         end;

         {chk
         for m := 0 to wooda.Count -1 do
         output.Add('wooda[' + InttoStr(m) + '].' + wooda[m] + '.');
         chk}

     {===================================================================}
     {Hand sorting the stringlist wooda which is itself the result of two
     sorts. A change detected from one entry to the next is flagged
     by noting the index value in the loop, and that value is interpreted
     as an index value in the stringlist eightblobs. The list of index
     values is caught in another stringlist, finalindex. Checking all 8
     positions is unnecessary, geometrically impossible, I believe. For
     hexahedrons limited to 4 points per face, two distinct hexes cannot
     share more than 4 points. However, the dupe-checking procedure does
     not work right unless the 5th place is also checked.}

       finalindex.Clear;

      for e := 0 to wooda.Count -2 do begin
      Label5.Caption := 'Working on reduction pass ' +InttoStr(e) + ' of ' +
      InttoStr(wooda.Count -2);
      Application.ProcessMessages;
      gofur := false;
      le1 := wooda[e];
      le2 := wooda[e +1];
      tib1 := GetToken(le1, ' ', 1);
      tib2 := GetToken(le1, ' ', 2);
      tib3 := GetToken(le1, ' ', 3);
      tib4 := GetToken(le1, ' ', 4);
      tib5 := GetToken(le1, ' ', 5);
    { tib6 := GetToken(le1, ' ', 6);
      tib7 := GetToken(le1, ' ', 7);
      tib8 := GetToken(le1, ' ', 8);  }
      tia1 := GetToken(le2, ' ', 1);
      tia2 := GetToken(le2, ' ', 2);
      tia3 := GetToken(le2, ' ', 3);
      tia4 := GetToken(le2, ' ', 4);
      tia5 := GetToken(le2, ' ', 5);
    { tia6 := GetToken(le2, ' ', 6);
      tia7 := GetToken(le2, ' ', 7);
      tia8 := GetToken(le2, ' ', 8); }
      if tib1 <> tia1 then gofur := true
      else if tib2 <> tia2 then gofur := true
      else if tib3 <> tia3 then gofur := true
      else if tib4 <> tia4 then gofur := true
      else if tib5 <> tia5 then gofur := true;
     { else if tib6 <> tia6 then gofur := true
      else if tib7 <> tia7 then gofur := true
      else if tib8 <> tia8 then gofur := true; }

      if gofur = true then begin
      sind := Copy(GetToken(le1, ' ', 9), 2, Length(GetToken(le1, ' ', 9)) -1);
      finalindex.Add(sind);
      gofur := false;
      end;
      end;

      Label5.Caption := 'Formulating results ' ;
      Application.ProcessMessages;

      {======================================================}
      {The method in the above block captures the last change
      but not the entry itself, which has to be specifically
      saved.}
      if wooda.Count > 0 then begin
      sind :=  Copy(GetToken(wooda[wooda.Count -1], ' ', 9), 2,
      Length(GetToken(wooda[wooda.Count -1], ' ', 9)) -1);
      finalindex.Add(sind);
      end;

      {chk
      for j := 0 to finalindex.Count -1 do
      output.Add('finalindex [' + InttoStr(j) + '] ' + finalindex[j]);
      chk}

      for j := 0 to finalindex.Count -1 do begin
      Label5.Caption := 'Populating element bank ' +InttoStr(j +1) + ' of ' +
      InttoStr(finalIndex.Count);
      Application.ProcessMessages;
      charz := eightblobs[StrtoInt(finalindex[j])];
      blobsworth.Add(' ' + GetToken(charz, ' ', 1) + ' ' +
      GetToken(charz, ' ', 2) + ' ' +
      GetToken(charz, ' ', 3) + ' ' +
      GetToken(charz, ' ', 4) + ' ' +
      GetToken(charz, ' ', 5) + ' ' +
      GetToken(charz, ' ', 6) + ' ' +
      GetToken(charz, ' ', 7) + ' ' +
      GetToken(charz, ' ', 8) + ' ');

      end;
      {chk
      for j := 0 to blobsworth.Count -1 do
      output.Add('blobsworth [' + InttoStr(j) + '] ' + blobsworth[j]);
      chk}

      {===========================================}


      numberofcells := blobsworth.Count;
      EnforceVerdictWinding(Sender);

      GetCellDimensions(Sender);

end;

procedure TForm1.GetCellDimensions(Sender: TObject);
var
   i, j : Integer;
   xmax, xmin, ymax, ymin, zmax, zmin : Double;
   xlen, ylen, zlen : String;
begin
   output.Add(' ');
   output.Add('CELLS' + ' ' + InttoStr(numberofcells) + ' ' +
   InttoStr(numberofcells * 9));

   for i := 0 to numberofcells -1 do begin
   output.Add('8' + blobsworth[i]);
   end;

   {Add the data for the block. This section is descriptive for interpretation
   by Paraview and other vtk clients, not exactly specific to IA-FEMesh.}

   if numberofcells = 0 then begin
   output.Add(' No elements were built. This could be the' + #10 +
   'result of duplicate vertices in the input.');
   end;

   output.Add(' ');
   output.Add('CELL_TYPES ' + InttoStr(numberofcells));
   for j := 1 to numberofcells do
   output.Add('12');

    if MenuItem9.Checked = true then begin

   output.Add(' ');
   output.Add('CELL_DATA ' + InttoStr(numberofcells));
   output.Add('FIELD FieldData 1');
   output.Add('Mesh_Seed 3 ' + InttoStr(numberofcells) + ' int');

   {The 'FieldData 1' descriptor refers to this being the only model data
   for this unstructured grid. I think 'Mesh_Seed 3' is the default level of
   element density for IA-FEMesh. No idea what 'int' means.}

   {The calculation of the dimensions of the cells. For rounding, I
   decided to use Ceil instead of Round, remembering the way IA-FEMesh cut
   into the too-small cage I first experimented with. However, I'm not sure
   that IA-FEMesh does it (rounds) exactly the same way.}

   for i := 0 to blobsworth.Count -1 do begin

   Label5.Caption := 'Calculating x attributes ' +InttoStr(i +1) + ' of ' +
      InttoStr(Blobsworth.Count);
      Application.ProcessMessages;

   xmax := Numarrayx[StrtoInt(GetToken(blobsworth[i], ' ', 2))];
   xmin := Numarrayx[StrtoInt(GetToken(blobsworth[i], ' ', 2))];
   for j := 3 to 9 do begin
   if Numarrayx[StrtoInt(GetToken(blobsworth[i], ' ', j))] > xmax then
   xmax := Numarrayx[StrtoInt(GetToken(blobsworth[i], ' ', j))];
   if Numarrayx[StrtoInt(GetToken(blobsworth[i], ' ', j))] < xmin then
   xmin := Numarrayx[StrtoInt(GetToken(blobsworth[i], ' ', j))];
   end;

   xlen := FloattoStr(Ceil(Abs(xmax -xmin)));
   xside.Add(xlen);

   end;

 {yyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyy below below below below below }

   for i := 0 to blobsworth.Count -1 do begin
   Label5.Caption := 'Calculating y attributes ' +InttoStr(i +1) + ' of ' +
      InttoStr(Blobsworth.Count);
      Application.ProcessMessages;

   ymax := Numarrayy[StrtoInt(GetToken(blobsworth[i], ' ', 2))];
   ymin := Numarrayy[StrtoInt(GetToken(blobsworth[i], ' ', 2))];
   for j := 3 to 9 do begin
   if Numarrayy[StrtoInt(GetToken(blobsworth[i], ' ', j))] > ymax then
   ymax := Numarrayy[StrtoInt(GetToken(blobsworth[i], ' ', j))];
   if Numarrayy[StrtoInt(GetToken(blobsworth[i], ' ', j))] < ymin then
   ymin := Numarrayy[StrtoInt(GetToken(blobsworth[i], ' ', j))];
   end;

   ylen := FloattoStr(Ceil(Abs(ymax -ymin)));
   yside.Add(ylen);

   end;

 {zzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzz below below below below below }

   for i := 0 to blobsworth.Count -1 do begin
   Label5.Caption := 'Calculating z attributes ' +InttoStr(i +1) + ' of ' +
      InttoStr(Blobsworth.Count);
      Application.ProcessMessages;

   zmax := Numarrayz[StrtoInt(GetToken(blobsworth[i], ' ', 2))];
   zmin := Numarrayz[StrtoInt(GetToken(blobsworth[i], ' ', 2))];
   for j := 3 to 9 do begin
   if Numarrayz[StrtoInt(GetToken(blobsworth[i], ' ', j))] > zmax then
   zmax := Numarrayz[StrtoInt(GetToken(blobsworth[i], ' ', j))];
   if Numarrayz[StrtoInt(GetToken(blobsworth[i], ' ', j))] < zmin then
   zmin := Numarrayz[StrtoInt(GetToken(blobsworth[i], ' ', j))];
   end;

   zlen := FloattoStr(Ceil(Abs(zmax -zmin)));
   zside.Add(zlen);

   end;


   for j := 0 to numberofcells -1 do
   sidecume.Add(xside[j] + ' ' + yside[j] + ' ' + zside[j]);

   for j := 0 to numberofcells -1 do

   output.Add(sidecume[j] + ' ');
   end
    else begin
      Label5.Caption := 'Conversion complete ' ;
      Application.ProcessMessages;
      end;

    Timer1StopTimer(Sender);

   {=====================}
   {The following sloppy way of freeing memory does not
   guarantee a leak-free program.  Best to restart the app
   before each required conversion.}
   xside.Free;
   yside.Free;
   zside.Free;
   sidecume.Free;
   vertlistf.Free;
   vertlists.Free;
   hopper1.Free;
   wooda.Free;
   Trigarray.Free;
   Trigarray2.Free;
   finalindex.Free;
   blobsworth.Free;

   Label5.Caption := 'Conversion complete ' ;
   Application.ProcessMessages;
   plyout := false;
   vtkout := true;


end;

procedure TForm1.Ply3WriteVtk(Sender: TObject);
var
   i : Integer;
   tempStr : String;
   vec1, vec2, maxvec : Double;
begin
 {  F := F3; }

   {Capture the string blobs which represent the connectivity of each face.
   These will be used later for constructing elements.}

   REPEAT
   tempStr := trim(SynEdit1.Lines[F]);
   vertlistf.Add(' ' + GetToken(tempStr, ' ', 2) + ' ' +
   GetToken(tempStr, ' ', 3) + ' ' +
   GetToken(tempStr, ' ', 4) + ' ');
   F := F + 1;
   until F = SynEdit1.Lines.Count {numberoffaces -i -2};

  { for i := 0 to vertlistf.Count -1 do begin
   Output.Add(vertlistf[i]);
   end;  }

   {Fill 3 arrays centroid-x,-y,-z of doubles with the coordinates of the
   centroids of all the faces. Find the largest intra-face point-to-point
   distance, maxvec, for each face and store in the array longvec. A
   mini-universe of face candidates will be created in the stringlist luniverse.
   To get in, for the working [i] face the centroid-to-centroid distance with the
   candidate must be less than radfac times the sum of the two maxvecs. This
   cuts down the searching greatly.}

   for i := 0 to vertlistf.Count -1 do begin
   centroidx[i] := 1/3 * (Numarrayx[StrtoInt(GetToken(vertlistf[i], ' ', 2))] +
   Numarrayx[StrtoInt(GetToken(vertlistf[i], ' ', 3))] +
   Numarrayx[StrtoInt(GetToken(vertlistf[i], ' ', 4))] );
   centroidy[i] := 1/3 * (Numarrayy[StrtoInt(GetToken(vertlistf[i], ' ', 2))] +
   Numarrayy[StrtoInt(GetToken(vertlistf[i], ' ', 3))] +
   Numarrayy[StrtoInt(GetToken(vertlistf[i], ' ', 4))] );
   centroidz[i] := 1/3 * (Numarrayz[StrtoInt(GetToken(vertlistf[i], ' ', 2))] +
   Numarrayz[StrtoInt(GetToken(vertlistf[i], ' ', 3))] +
   Numarrayz[StrtoInt(GetToken(vertlistf[i], ' ', 4))] );

   vec1 := Sqrt((Numarrayx[StrtoInt(GetToken(vertlistf[i], ' ', 2))] -
   Numarrayx[StrtoInt(GetToken(vertlistf[i], ' ', 3))]) *
   (Numarrayx[StrtoInt(GetToken(vertlistf[i], ' ', 2))] -
   Numarrayx[StrtoInt(GetToken(vertlistf[i], ' ', 3))])   +
   (Numarrayy[StrtoInt(GetToken(vertlistf[i], ' ', 2))] -
   Numarrayy[StrtoInt(GetToken(vertlistf[i], ' ', 3))]) *
   (Numarrayy[StrtoInt(GetToken(vertlistf[i], ' ', 2))] -
   Numarrayy[StrtoInt(GetToken(vertlistf[i], ' ', 3))])   +
   (Numarrayz[StrtoInt(GetToken(vertlistf[i], ' ', 2))] -
   Numarrayz[StrtoInt(GetToken(vertlistf[i], ' ', 3))]) *
   (Numarrayz[StrtoInt(GetToken(vertlistf[i], ' ', 2))] -
   Numarrayz[StrtoInt(GetToken(vertlistf[i], ' ', 3))])   );

   vec2 := Sqrt((Numarrayx[StrtoInt(GetToken(vertlistf[i], ' ', 2))] -
   Numarrayx[StrtoInt(GetToken(vertlistf[i], ' ', 4))]) *
   (Numarrayx[StrtoInt(GetToken(vertlistf[i], ' ', 2))] -
   Numarrayx[StrtoInt(GetToken(vertlistf[i], ' ', 4))])   +
   (Numarrayy[StrtoInt(GetToken(vertlistf[i], ' ', 2))] -
   Numarrayy[StrtoInt(GetToken(vertlistf[i], ' ', 4))]) *
   (Numarrayy[StrtoInt(GetToken(vertlistf[i], ' ', 2))] -
   Numarrayy[StrtoInt(GetToken(vertlistf[i], ' ', 4))])   +
   (Numarrayz[StrtoInt(GetToken(vertlistf[i], ' ', 2))] -
   Numarrayz[StrtoInt(GetToken(vertlistf[i], ' ', 4))]) *
   (Numarrayz[StrtoInt(GetToken(vertlistf[i], ' ', 2))] -
   Numarrayz[StrtoInt(GetToken(vertlistf[i], ' ', 4))])   );

   maxvec := vec1;
   if (vec1 > vec2) then maxvec := vec1
   else if (vec2 > vec1)  then maxvec := vec2;

   longvec[i] := maxvec;
   end;

   Searchfor3Edge(Sender);

end;

procedure TForm1.Searchfor3Edge(Sender: TObject);
var a, i, k, s, e, d, b, c, t1, t2, t3, a1int,
   a3int, a2int, otherone, closure : Integer;
   a1, a2, a3, concatp : String;

    pvol : Double;

begin
  radfac := StrtoInt(MaskEdit1.Text);


   {====================================================================}
      {A big loop. The collection of faces is worked on one by one in the
       i loop. }

      for i := 0 to vertlistf.Count -1 do begin

       Label5.Caption := 'Working on face ' +InttoStr(i +1) + ' of ' +
       InttoStr(numberoffaces);
       Application.ProcessMessages;

      luniverse.Clear;

      {chk
      output.Add('****************************************'
      + '**************************');
      chk}

      {==============================================}
      {a1-a2 is an edge.  An adjacent edge is a2-a3}

      a1 := GetToken(vertlistf[i], ' ', 2);
      a2 := GetToken(vertlistf[i], ' ', 3);
      a3 := GetToken(vertlistf[i], ' ', 4);

      {The luniverse stringlist is populated. Using a factor of 'radfac' to decide
      whether to include will miss elements with aspect ratio greater than that,
      which is could be a considerable number.}

      for e := 0 to vertlistf.Count -1 do begin
      if e <> i then
      if Sqrt(sqr(centroidx[i] -centroidx[e]) + sqr(centroidy[i] -centroidy[e])
        + sqr(centroidz[i] -centroidz[e])) <
      radfac * (longvec[i] + longvec[e]) then luniverse.Add(vertlistf[e]);
      end;

      Trigarray.Clear;
      oneedge.Clear;
      twoedge.Clear;

       {====================================================================}
      {chk
      output.Add('vertlistf.count ' + InttoStr(vertlistf.count));
      output.Add('vertlistf[' + InttoStr(i) + '] .' + vertlistf[i]);
      output.Add('a1= ' + a1 + ' a2= ' + a2 + ' a3= ' + a3);
      chk}
     { for e := 0 to vertlistf.Count -1 do
      output.Add('vertlistf ' + InttoStr(e) + ' ' + vertlistf[e]);  }

      for d := 0 to luniverse.Count -1 do begin
      if (AnsiPos(' ' + a1 + ' ', luniverse[d]) <> 0) then
      if (AnsiPos(' ' + a2 + ' ', luniverse[d]) <> 0) then
      if luniverse[d] <> vertlistf[i] then begin
      Trigarray.Add(luniverse[d]);
      end;
      end;

      {chk
      for k := 0 to Trigarray.Count -1 do
      output.Add('Trigarray[' + InttoStr(k) + '] ' + Trigarray[k]);
      chk}

      for b := 0 to luniverse.Count -1 do begin
      if (AnsiPos(' ' + a2 + ' ', luniverse[b]) <> 0) then
      if (AnsiPos(' ' + a3 + ' ', luniverse[b])<> 0) then
      if luniverse[b] <> vertlistf[i] then begin
      oneedge.Add(luniverse[b]);
      end;
      end;
      {for g := 0 to oneedge.Count -1 do
      output.Add('oneedge[' + InttoStr(g) + '] ' + oneedge[g]);}

      for c := 0 to luniverse.Count -1 do begin
      if (AnsiPos(' ' + a3 + ' ', luniverse[c]) <> 0) then
      if (AnsiPos(' ' + a1 + ' ', luniverse[c])<> 0) then
      if luniverse[c] <> vertlistf[i] then begin
      twoedge.Add(luniverse[c]);
      end;
      end;
      {for g := 0 to twoedge.Count -1 do
      output.Add('twoedge[' + InttoStr(g) + '] ' + twoedge[g]); }

       {=======================================================================}
      {Do the sleuthing. Ansipos works nicely to keep the middle section of
      the block short. Integers are used for comparing variable
      values where possible, because, last I heard, 'AND' logical
      constructs don't work with strings.}

       for s := 0 to Trigarray.Count -1 do begin
       closure := 0;

       t1 := StrtoInt(GetToken(Trigarray[s], ' ', 2));
       t2 := StrtoInt(GetToken(Trigarray[s], ' ', 3));
       t3 := StrtoInt(GetToken(Trigarray[s], ' ', 4));
       a3int := StrtoInt(a3);
       a2int := StrtoInt(a2);
       a1int := StrtoInt(a1);

       if (t1 <> StrtoInt(a1)) AND (t1 <> StrtoInt(a2)) then otherone :=
         (t1) else
       if (t2 <> StrtoInt(a1)) AND (t2 <> StrtoInt(a2)) then otherone :=
         (t2) else
       if (t3 <> StrtoInt(a1)) AND (t3 <> StrtoInt(a2)) then otherone :=
         (t3);
       concatp :=  ' ' + a1 + ' ' + a2 + ' ' + a3 + ' ' ;

       for a := 0 to oneedge.Count -1 do begin
       if Ansipos(' ' + InttoStr(otherone) + ' ', oneedge[a]) <> 0
         then closure := closure +1;
       end;

       for k := 0 to twoedge.Count -1 do begin
       if Ansipos(' ' + InttoStr(otherone) + ' ', twoedge[k]) <> 0
        then closure := closure +1;
       end;
     {  output.Add('pvol ' + FloattoStr(pvol));  }

       if closure > 1 then begin
       pvol := CheckVol(a1int, a2int, a3int, otherone);
      { output.Add('pvol ' + FloattoStr(pvol)); }
       if (Ansipos(' ' + InttoStr(otherone) + ' ', concatp) = 0) AND
         (pvol > 0.001) then
         eightblobs3.Add(vertlistf[i] + InttoStr(otherone));
       end;

       end; {for s := 0 to Trigarray.Count -1 do begin}
       end; {for i := 0 to vertlistf.Count -1 do begin}

      { for w := 0 to eightblobs3.Count -1 do }
       { eightblobs[w] := (eightblobs3[w]);
      for i := 0 to eightblobs3.Count -1 do  }
     { output.Add('****eightblobs3 ' + InttoStr(w) + ' ' + eightblobs3[w]);}
      Process3EightBlobs(Sender);

end;

procedure TForm1.Process3EightBlobs(Sender: TObject);
var
   e, s, j, m, rack, i : Integer;
   gofur : Boolean;
   tib1, tib2, tib3, tib4, tia1, tia2, tia3, tia4,
   le1, le2, sind, charz : String;
begin

   { for m := 0 to eightblobs3.Count -1 do
    output.Add('eightblobs3 ' + InttoStr(m) + ' ' + eightblobs3[m]); }

  for m := 0 to eightblobs3.Count -1 do
        eightblobs[m] := Trim(eightblobs3[m]);

        for e := 0 to eightblobs3.Count -1 do begin
        if eightblobs[e] <> '' then
        eightblobs[e] := eightblobs[e] + ' z' + InttoStr(e);
        end;

        wooda.Clear;
      {  try  }
      { for i := 0 to eightblobs3.Count -1 do
      output.Add('****eightblobs ' + InttoStr(i) + ' ' + eightblobs[i]);  }
      {Indexing an array is somewhat tricky. Since the array was populated
      one-for-one from a stringlist, that stringlist is tapped for the
      indexing.}
        for s := 0 to eightblobs3.Count -1 do begin
        if eightblobs[s] <> '' then begin
        hopper1.Clear;

        hopper1.Add(GetToken(eightblobs[s], ' ', 1));
        hopper1.Add(GetToken(eightblobs[s], ' ', 2));
        hopper1.add(GetToken(eightblobs[s], ' ', 3));
        hopper1.add(GetToken(eightblobs[s], ' ', 4));
        hopper1.add(GetToken(eightblobs[s], ' ', 5));

        wooda.Add(hopper1[0] + ' ' +
        hopper1[1] + ' ' +
        hopper1[2] + ' ' +
        hopper1[3] + ' ' +
        hopper1[4]
        );
       { If the above line throws an out-of-range error it may be
       because there is a duplication of one of the blobs, which
       hopper1 has chopped off.}
        end;
        end;

      {  except
           on e: EStringListError do
           MyShowMessage('Exception thrown here may' + #10 +
           ' mean duplicate vertices in the input' + #10 +
           ' or possibly unflatness problems. %s' , ['']);
         end; }
         {chk
         for m := 0 to wooda.Count -1 do
         output.Add('wooda[' + InttoStr(m) + '].' + wooda[m] + '.');
         chk}

        finalindex.Clear;
      { for s := 0 to wooda.Count -1 do
       output.Add('wooda ' + wooda[s]);  }

      { for i := 0 to wooda.Count -1 do
        output.Add('eightblobs ' + eightblobs[i]); }

      for e := 0 to wooda.Count -2 do begin
      Label5.Caption := 'Working on reduction pass ' +InttoStr(e +1) + ' of ' +
      InttoStr(wooda.Count -1);
      Application.ProcessMessages;
      gofur := false;
      le1 := wooda[e];
      le2 := wooda[e +1];
      tib1 := GetToken(le1, ' ', 1);
      tib2 := GetToken(le1, ' ', 2);
      tib3 := GetToken(le1, ' ', 3);
      tib4 := GetToken(le1, ' ', 4);

      tia1 := GetToken(le2, ' ', 1);
      tia2 := GetToken(le2, ' ', 2);
      tia3 := GetToken(le2, ' ', 3);
      tia4 := GetToken(le2, ' ', 4);

      if tib1 <> tia1 then gofur := true
      else if tib2 <> tia2 then gofur := true
      else if tib3 <> tia3 then gofur := true
      else if tib4 <> tia4 then gofur := true;

      if gofur = true then begin
      sind := Copy(GetToken(le1, ' ', 5), 2, Length(GetToken(le1, ' ', 5)) -1);
      finalindex.Add(sind);
      gofur := false;
      end;
      end;


      Label5.Caption := 'Formulating results ' ;
      Application.ProcessMessages;

      {======================================================}
      {The method in the above block captures the last change
      but not the entry itself, which has to be specifically
      saved.}
      if wooda.Count > 0 then begin
      sind :=  Copy(GetToken(wooda[wooda.Count -1], ' ', 5), 2,
      Length(GetToken(wooda[wooda.Count -1], ' ', 5)) -1);
      finalindex.Add(sind);
      end;

      {chk
      for j := 0 to finalindex.Count -1 do
      output.Add('finalindex [' + InttoStr(j) + '] ' + finalindex[j]);
      chk}

      for j := 0 to finalindex.Count -1 do begin
      Label5.Caption := 'Populating element bank ' +InttoStr(j +1) + ' of ' +
      InttoStr(finalIndex.Count);
      Application.ProcessMessages;
      charz := eightblobs[StrtoInt(finalindex[j])];
      blobsworth.Add(' ' + GetToken(charz, ' ', 1) + ' ' +
      GetToken(charz, ' ', 2) + ' ' +
      GetToken(charz, ' ', 3) + ' ' +
      GetToken(charz, ' ', 4) + ' ');

      end;
      {chk
      for j := 0 to blobsworth.Count -1 do
      output.Add('blobsworth [' + InttoStr(j) + '] ' + blobsworth[j]);
      chk}

      for m := 0 to blobsworth.Count -1 do begin
       charz := trim(blobsworth[m]);
      rack := GetWinding(GetToken(charz, ' ', 1), GetToken(charz, ' ', 2),
      GetToken(charz, ' ', 3), GetToken(charz, ' ', 4));
      if rack > 0 then
      blobsworth[m] :=  ' ' + GetToken(charz, ' ', 2) + ' ' +
      GetToken(charz, ' ', 1) + ' ' + GetToken(charz, ' ', 3) + ' ' +
      GetToken(charz, ' ', 4) + ' ';
      end;
      {chk
      for j := 0 to blobsworth.Count -1 do
      output.Add('blobsworth updated [' + InttoStr(j) + '].' + blobsworth[j]
      + '.');
      chk}

     numberofcells := blobsworth.Count;

     output.Add(' ');
     output.Add('CELLS' + ' ' + InttoStr(numberofcells) + ' ' +
     InttoStr(numberofcells * 5));

     for i := 0 to numberofcells -1 do begin
     output.Add('4' + blobsworth[i]);
     end;

     output.Add(' ');
     output.Add('CELL_TYPES ' + InttoStr(numberofcells));
     for j := 1 to numberofcells do
     output.Add('10');

     Label5.Caption := 'Conversion complete ' ;
      Application.ProcessMessages;

   xside.Free;
   yside.Free;
   zside.Free;
   sidecume.Free;
   vertlistf.Free;
   vertlists.Free;
   hopper1.Free;
   wooda.Free;
   Trigarray.Free;
   Trigarray2.Free;
   finalindex.Free;
   blobsworth.Free;
   eightblobs3.Free;
   oneedge.Free;
   twoedge.Free;

   Timer1StopTimer(Sender);
   plyout := false;
   vtkout := true;

end;


procedure TForm1.MyShowMessage(Const Fmt : String; const Args : Array of const);

begin

  ShowMessage(format(Fmt,Args))

end;

procedure TForm1.VtkWritePly(Sender: TObject);
var
   t, j : Integer;
   tempStr : String;

begin
   Timer1.Enabled := true;
   ElapsedT := 0;
   Timer1StartTimer(Sender);

   eightblobsf := TStringlist.Create; {list where orig connectivity is preserved}
   eightblobsf.Sorted := false;
   eightblobsf.Duplicates := dupAccept;
   eightblobsf.Clear;
   eightblobsl := TStringlist.Create; {list where orig connectivity is preserved}
   eightblobsl.Sorted := false;
   eightblobsl.Duplicates := dupAccept;
   eightblobsl.Clear;
   hopper1 := TStringlist.Create; {sorting all the blobs in each face}
   hopper1.Sorted := true;
   hopper1.Duplicates := dupIgnore;
   hopper1.Clear;
   wooda := TStringlist.Create; {sorting the faces as whole faces}
   wooda.Sorted := true;
   wooda.Duplicates := dupIgnore;
   wooda.Clear;
   finalindex := TStringlist.Create; {distinct index to eightblobsl position}
   finalindex.Sorted := false;
   finalindex.Duplicates := dupAccept;
   finalindex.Clear;
   blobsworth := TStringlist.Create; {final list of unique face lists}
   blobsworth.Sorted := false;
   blobsworth.Duplicates := dupAccept;
   blobsworth.Clear;
   vertlistf := TStringlist.Create; {holding list for coords}
   vertlistf.Sorted := false;
   vertlistf.Duplicates := dupAccept;
   vertlistf.Clear;
   output := TStringlist.Create; {holding list for coords}
   output.Sorted := false;
   output.Duplicates := dupAccept;
   output.Clear;

   Label5.visible := true;
      {Label1.Caption := 'Working on face ' +InttoStr(j +1) + ' of ' +
      InttoStr(finalindex.Count);}
      Label5.Caption := 'Step 1 of 4: gather information.';
      Application.ProcessMessages;

   F := 1;

   output.Add('ply');
   output.Add('format ascii 1.0');
   output.Add('comment created by Blenbridge');

   {Get the number of verts}
   REPEAT
   tempStr := trim(SynEdit1.Lines[F]);
   if AnsiPos('POINTS', tempStr) = 0 then
   F := F + 1;
   until AnsiPos('POINTS', tempStr) <> 0;

   numberofverts := StrtoInt(GetToken(tempStr, ' ', 2));

   output.Add('element vertex ' + InttoStr(numberofverts));
   output.Add('property float x ');
   output.Add('property float y ');
   output.Add('property float z ');

    {Get the number of cells.}

   REPEAT
   tempStr := trim(SynEdit1.Lines[F]);
   if AnsiPos('CELLS', tempStr) = 0 then
   F := F + 1;
   until (AnsiPos('CELLS', tempStr) <> 0) OR (F = SynEdit1.Lines.Count);

   numberofcells := StrtoInt(GetToken(tempStr, ' ', 2));

  { F := 5; }
   F := 1;
   j := 0;

   REPEAT
   tempStr := trim(SynEdit1.Lines[F]);
   if AnsiPos('POINTS', tempStr) = 0 then
   F := F + 1;
   until (AnsiPos('POINTS', tempStr) <> 0) OR (F = SynEdit1.Lines.Count);

   F := F +1;

   {Capture the coords of the verts.  Print them out.}
   {Just saving the coord info in case I want to use it later. I could just
   print out the coords, here, problem is that the number of faces must be
   printed in the .ply file before the vertex coords are printed. So I have
   to stick them in a stringlist for the time being.}

   REPEAT
   tempStr := trim(SynEdit1.Lines[F]);

  { Numarrayx[i] := StrtoFloat(GetToken(tempStr, ' ', 1));
   Numarrayy[i] := StrtoFloat(GetToken(tempStr, ' ', 2));
   Numarrayz[i] := StrtoFloat(GetToken(tempStr, ' ', 3)); }
   vertlistf.Add(GetToken(tempStr, ' ', 1) + ' ' +
   GetToken(tempStr, ' ', 2) + ' ' +
   GetToken(tempStr, ' ', 3));
   t := 1;

   if GetToken(tempStr, ' ', 4) <> '' then begin
  { i := i +1; }
 {  Numarrayx[i] := StrtoFloat(GetToken(tempStr, ' ', 4));
   Numarrayy[i] := StrtoFloat(GetToken(tempStr, ' ', 5));
   Numarrayz[i] := StrtoFloat(GetToken(tempStr, ' ', 6)); }
   vertlistf.Add(GetToken(tempStr, ' ', 4) + ' ' +
   GetToken(tempStr, ' ', 5) + ' ' +
   GetToken(tempStr, ' ', 6));
   t := 2;
   end;

   if GetToken(tempStr, ' ', 7)<> '' then begin
  { i := i +1; }
{   Numarrayx[i] := StrtoFloat(GetToken(tempStr, ' ', 7));
   Numarrayy[i] := StrtoFloat(GetToken(tempStr, ' ', 8));
   Numarrayz[i] := StrtoFloat(GetToken(tempStr, ' ', 9)); }
   vertlistf.Add(GetToken(tempStr, ' ', 7) + ' ' +
   GetToken(tempStr, ' ', 8) + ' ' +
   GetToken(tempStr, ' ', 9));
   t := 3;
   end;

   j := j +t;
   F := F +1;
   until j = numberofverts;

   REPEAT
   tempStr := trim(SynEdit1.Lines[F]);
   if AnsiPos('CELLS', tempStr) = 0 then
   F := F + 1;
   until (AnsiPos('CELLS', tempStr) <> 0) OR (F = SynEdit1.Lines.Count);

   F := F +1;
   F3 := F;

   begin
   tempStr := trim(SynEdit1.Lines[F]);
   if GetToken(tempStr, ' ', 1) = '8' then WritePly4Faces(Sender)
   else if GetToken(tempStr, ' ', 1) = '4' then WritePly3Faces(Sender)
   else if GetToken(tempStr, ' ', 1) = '3' then WritePlyTri(Sender)

   else Label5.Caption := 'Path choice error line 1924';
   end;


  end;

procedure TForm1.WritePly4Faces(Sender: TObject);
var
   tempStr, le1, le2, tib1, tib2, tib3, tib4, tia1, tia2, tia3, tia4,
   sind, charz : String;
   gofur : Boolean;
   i, j : Integer;
begin

   {The other problem with the conversion. It is easy to unscramble a .vtk
   file and get well-ordered faces. However, that is figuring on 6 faces per
   cell, and there will be duplicates.  Blender will get rid of the duplicates
   automatically, but Paraview will not, and it is awkward seeing excess of
   faces reported.  Therefore a culling procedure similar to the one in the .ply
   to .vtk direction.}
   Label5.Caption := 'Step 2 of 4: formulate face sequences.';
   Application.ProcessMessages;

   i := 0;

   REPEAT
   tempStr := trim(SynEdit1.Lines[F]);

   eightblobsf.Add(GetToken(tempStr, ' ', 2) + ' ' +
   GetToken(tempStr, ' ', 3) + ' ' +
   GetToken(tempStr, ' ', 4) + ' ' +
   GetToken(tempStr, ' ', 5) + ' ' +
   GetToken(tempStr, ' ', 6) + ' ' +
   GetToken(tempStr, ' ', 7) + ' ' +
   GetToken(tempStr, ' ', 8) + ' ' +
   GetToken(tempStr, ' ', 9));

   eightblobsl.Add( GetToken(tempStr, ' ', 2) + ' ' +
   GetToken(tempStr, ' ', 3) + ' ' +
   GetToken(tempStr, ' ', 4) + ' ' +
   GetToken(tempStr, ' ', 5));
   eightblobsl.Add(GetToken(tempStr, ' ', 6) + ' ' +
   GetToken(tempStr, ' ', 7) + ' ' +
   GetToken(tempStr, ' ', 8) + ' ' +
   GetToken(tempStr, ' ', 9));
   eightblobsl.Add(GetToken(tempStr, ' ', 4) + ' ' +
   GetToken(tempStr, ' ', 5) + ' ' +
   GetToken(tempStr, ' ', 9) + ' ' +
   GetToken(tempStr, ' ', 8));
   eightblobsl.Add(GetToken(tempStr, ' ', 2) + ' ' +
   GetToken(tempStr, ' ', 3) + ' ' +
   GetToken(tempStr, ' ', 7) + ' ' +
   GetToken(tempStr, ' ', 6));
   eightblobsl.Add(GetToken(tempStr, ' ', 3) + ' ' +
   GetToken(tempStr, ' ', 4) + ' ' +
   GetToken(tempStr, ' ', 8) + ' ' +
   GetToken(tempStr, ' ', 7));
   eightblobsl.Add(GetToken(tempStr, ' ', 2) + ' ' +
   GetToken(tempStr, ' ', 5) + ' ' +
   GetToken(tempStr, ' ', 9) + ' ' +
   GetToken(tempStr, ' ', 6));

   F := F +1;
   i := i +1;
   until i = numberofcells;

   for j := 0 to eightblobsl.Count -1 do
   eightblobsl[j] := eightblobsl[j] + ' z' + InttoStr(j);

   Label5.Caption := 'Step 3 of 4: remove duplicate faces.';
   Application.ProcessMessages;
   for i := 0 to eightblobsl.Count -1 do begin
        hopper1.Clear;

        hopper1.Add(GetToken(eightblobsl[i], ' ', 1));
        hopper1.Add(GetToken(eightblobsl[i], ' ', 2));
        hopper1.add(GetToken(eightblobsl[i], ' ', 3));
        hopper1.add(GetToken(eightblobsl[i], ' ', 4));
        hopper1.add(GetToken(eightblobsl[i], ' ', 5));

        wooda.Add(hopper1[0] + ' ' +
        hopper1[1] + ' ' +
        hopper1[2] + ' ' +
        hopper1[3] + ' ' +
        hopper1[4] );

        Application.ProcessMessages;
        end;

     finalindex.Clear;

      for i := 0 to wooda.Count -2 do begin
       gofur := false;
      le1 := wooda[i];
      le2 := wooda[i +1];
      tib1 := GetToken(le1, ' ', 1);
      tib2 := GetToken(le1, ' ', 2);
      tib3 := GetToken(le1, ' ', 3);
      tib4 := GetToken(le1, ' ', 4);

      tia1 := GetToken(le2, ' ', 1);
      tia2 := GetToken(le2, ' ', 2);
      tia3 := GetToken(le2, ' ', 3);
      tia4 := GetToken(le2, ' ', 4);

      if tib1 <> tia1 then gofur := true
      else if tib2 <> tia2 then gofur := true
      else if tib3 <> tia3 then gofur := true
      else if tib4 <> tia4 then gofur := true;

      if gofur = true then begin
      sind := Copy(GetToken(le1, ' ', 5), 2, Length(GetToken(le1, ' ', 5)) -1);
      finalindex.Add(sind);
      gofur := false;
      end;
      Application.ProcessMessages;
      end;

      sind :=  Copy(GetToken(wooda[wooda.Count -1], ' ', 5), 2,
      Length(GetToken(wooda[wooda.Count -1], ' ', 5)) -1);
      finalindex.Add(sind);

      Label5.Caption := 'Step 4 of 4: write faces.';
      Application.ProcessMessages;
      for j := 0 to finalindex.Count -1 do begin

      charz := eightblobsl[StrtoInt(finalindex[j])];
      blobsworth.Add(' ' + GetToken(charz, ' ', 1) + ' ' +
      GetToken(charz, ' ', 2) + ' ' +
      GetToken(charz, ' ', 3) + ' ' +
      GetToken(charz, ' ', 4) + ' ' );
      end;

      {below: the numberoffaces variable is not needed.}

      output.Add('element face ' + InttoStr(Blobsworth.Count));
      output.Add('property list uchar uint vertex_indices');
      output.Add('end_header ');
      for i := 0 to vertlistf.Count -1 do
      output.Add(vertlistf[i]);
      for j := 0 to blobsworth.Count -1 do
      output.Add('4' + blobsworth[j]);
      for i := 0 to eightblobsf.Count -1 do begin
      output.Add('3' + ' ' + GetToken(eightblobsf[i], ' ', 1) + ' ' +
         GetToken(eightblobsf[i], ' ', 2) + ' ' +
         GetToken(eightblobsf[i], ' ', 3));
      output.Add('3' + ' ' + GetToken(eightblobsf[i], ' ', 1) + ' ' +
         GetToken(eightblobsf[i], ' ', 3) + ' ' +
         GetToken(eightblobsf[i], ' ', 4));
      output.Add('3' + ' ' + GetToken(eightblobsf[i], ' ', 5) + ' ' +
         GetToken(eightblobsf[i], ' ', 6) + ' ' +
         GetToken(eightblobsf[i], ' ', 7));
      output.Add('3' + ' ' + GetToken(eightblobsf[i], ' ', 6) + ' ' +
         GetToken(eightblobsf[i], ' ', 7) + ' ' +
         GetToken(eightblobsf[i], ' ', 8));
      end;

      eightblobsl.Free;
      hopper1.Free;
      wooda.Free;
      finalindex.Free;
      blobsworth.Free;
      vertlistf.Free;

      Label5.Caption := 'Conversion complete ' ;
      Application.ProcessMessages;
      Timer1StopTimer(Sender);
      vtkout := false;
      plyout := true;


end;

procedure TForm1.WritePly3Faces(Sender: TObject);

{This procedure started out as a way to translate tetrahedral mesh to .ply
format. It was 'see four verts, write a ply tet.' But then I realized that
four verts could also be a quad, and it became desirable to translate quads for
checking mesh quality. So there is a fork to do both in here. For reference,
the vtk code for hex = 12; tet = 10, quad = 9, tri = 5.}

var
   tempStr, le1, le2, tib1, tib2, tib3, tib4, tia1, tia2, tia3, tia4,
   sind, charz : String;
   gofur, flat : Boolean;
   i, j, rem : Integer;
begin
   Label5.Caption := 'Step 2 of 4: formulate face sequences.';
   Application.ProcessMessages;

   i := 0;
   rem := F - F3;
   eightblobsl.Clear;
   flat := false;

   REPEAT
   tempStr := trim(SynEdit1.Lines[F]);
   if AnsiPos('CELL_TYPES', tempStr) = 0 then
   F := F + 1;
   until (AnsiPos('CELL_TYPES', tempStr) <> 0) OR (F = SynEdit1.Lines.Count);

   F := F +1;

   tempStr := trim(SynEdit1.Lines[F]);
   if  GetToken(tempStr, ' ', 1) = '9' then begin
   flat := true;
   end;

   F := 1;

   REPEAT
   tempStr := trim(SynEdit1.Lines[F]);
   if AnsiPos('CELLS', tempStr) = 0 then
   F := F + 1;
   until (AnsiPos('CELLS', tempStr) <> 0) OR (F = SynEdit1.Lines.Count);

   F := F +1;

   if flat = true then begin

   REPEAT
   tempStr := trim(SynEdit1.Lines[F]);
   eightblobsl.Add( GetToken(tempStr, ' ', 2) + ' ' +
   GetToken(tempStr, ' ', 3) + ' ' +
   GetToken(tempStr, ' ', 4) + ' ' + GetToken(tempStr, ' ', 5));

   F := F +1;
   i := i +1;

   until i >= numberofcells - rem;

   for j := 0 to eightblobsl.Count -1 do begin
   blobsworth.Add(eightblobsl[j]);
   end;

   output.Add('element face ' + InttoStr(Blobsworth.Count));
      output.Add('property list uchar uint vertex_indices');
      output.Add('end_header ');
      for i := 0 to vertlistf.Count -1 do
      output.Add(vertlistf[i]);
      for j := 0 to blobsworth.Count -1 do
      output.Add('4' + ' ' + blobsworth[j]);

   end
   else if flat = false then begin

   REPEAT
   tempStr := trim(SynEdit1.Lines[F]);
   eightblobsl.Add( GetToken(tempStr, ' ', 2) + ' ' +
   GetToken(tempStr, ' ', 3) + ' ' +
   GetToken(tempStr, ' ', 4));
   eightblobsl.Add(GetToken(tempStr, ' ', 2) + ' ' +
   GetToken(tempStr, ' ', 3) + ' ' +
   GetToken(tempStr, ' ', 5));
   eightblobsl.Add(GetToken(tempStr, ' ', 3) + ' ' +
   GetToken(tempStr, ' ', 4) + ' ' +
   GetToken(tempStr, ' ', 5));
   eightblobsl.Add(GetToken(tempStr, ' ', 4) + ' ' +
   GetToken(tempStr, ' ', 5) + ' ' +
   GetToken(tempStr, ' ', 2));

   F := F +1;
   i := i +1;
   until i >= numberofcells - rem;

   for j := 0 to eightblobsl.Count -1 do
   eightblobsl[j] := eightblobsl[j] + ' z' + InttoStr(j);
   {chk
   for j := 0 to eightblobsl.Count -1 do
   output.Add('eightblobsl ' + InttoStr(j) + ' ' + eightblobsl[j]);
   output.Add('rem ' + InttoStr(rem));
   output.Add('numberofcells ' + InttoStr(numberofcells));
   chk}
   Label5.Caption := 'Step 3 of 4: remove duplicate faces.';
   Application.ProcessMessages;
   for i := 0 to eightblobsl.Count -1 do begin
        hopper1.Clear;

        hopper1.Add(GetToken(eightblobsl[i], ' ', 1));
        hopper1.Add(GetToken(eightblobsl[i], ' ', 2));
        hopper1.add(GetToken(eightblobsl[i], ' ', 3));
        hopper1.add(GetToken(eightblobsl[i], ' ', 4));

        wooda.Add(hopper1[0] + ' ' +
        hopper1[1] + ' ' +
        hopper1[2] + ' ' +
        hopper1[3] );

        Label5.Caption := 'Working on reduction pass ' + InttoStr(i +1) + ' of '
        + InttoStr(eightblobsl.Count) + ' passes.';
        Application.ProcessMessages;
        end;
      {chk
      for j := 0 to wooda.Count -1 do
         output.Add('wooda[' + InttoStr(j) + '].' + wooda[j] + '.');
      chk}

   finalindex.Clear;
        {   Label5.Caption := 'past finalindex.clear';
   Application.ProcessMessages; }
      for i := 0 to wooda.Count -2 do begin
       gofur := false;
      le1 := wooda[i];
      le2 := wooda[i +1];
      tib1 := GetToken(le1, ' ', 1);
      tib2 := GetToken(le1, ' ', 2);
      tib3 := GetToken(le1, ' ', 3);
      tib4 := GetToken(le1, ' ', 4);

      tia1 := GetToken(le2, ' ', 1);
      tia2 := GetToken(le2, ' ', 2);
      tia3 := GetToken(le2, ' ', 3);
      tia4 := GetToken(le2, ' ', 4);

      if tib1 <> tia1 then gofur := true
      else if tib2 <> tia2 then gofur := true
      else if tib3 <> tia3 then gofur := true
      else if tib4 <> tia4 then gofur := true;

      if gofur = true then begin
      sind := Copy(GetToken(le1, ' ', 4), 2, Length(GetToken(le1, ' ', 4)) -1);
      finalindex.Add(sind);
      gofur := false;
      end;
      end;

      sind :=  Copy(GetToken(wooda[wooda.Count -1], ' ', 4), 2,
      Length(GetToken(wooda[wooda.Count -1], ' ', 4)) -1);
      finalindex.Add(sind);

      Label5.Caption := 'Step 4 of 4: write faces.';
      Application.ProcessMessages;

      for j := 0 to finalindex.Count -1 do begin
      charz := eightblobsl[StrtoInt(finalindex[j])];
      blobsworth.Add(' ' + GetToken(charz, ' ', 1) + ' ' +
      GetToken(charz, ' ', 2) + ' ' +
      GetToken(charz, ' ', 3) + ' ' );
      end;

      output.Add('element face ' + InttoStr(Blobsworth.Count));
      output.Add('property list uchar uint vertex_indices');
      output.Add('end_header ');
      for i := 0 to vertlistf.Count -1 do
      output.Add(vertlistf[i]);
      for j := 0 to blobsworth.Count -1 do
      output.Add('3' + blobsworth[j]);
      end;     {else if flat = false then begin   }

      eightblobsl.Free;
      hopper1.Free;
      wooda.Free;
      finalindex.Free;
      blobsworth.Free;
      vertlistf.Free;

      Label5.Caption := 'Conversion complete ' ;
      Application.ProcessMessages;
      Timer1StopTimer(Sender);
      vtkout := false;
      plyout := true;


  end;

procedure TForm1.WritePlyTri(Sender: TObject);
{Objective is to convert triangular .vtk faces into .ply format so that on
import they will stick to mesh faces in Blender and can easily be eliminated.}
var i, j : Integer;
   tempStr : String;
begin
   i := 0;
   eightblobsl.Clear;

   REPEAT
   tempStr := trim(SynEdit1.Lines[F]);
   eightblobsl.Add( GetToken(tempStr, ' ', 2) + ' ' +
   GetToken(tempStr, ' ', 3) + ' ' +
   GetToken(tempStr, ' ', 4));

   F := F +1;
   i := i +1;

   until i >= numberofcells;

   for j := 0 to eightblobsl.Count -1 do
   blobsworth.Add(eightblobsl[j]);

   output.Add('element face ' + InttoStr(Blobsworth.Count));
      output.Add('property list uchar uint vertex_indices');
      output.Add('end_header ');
      for i := 0 to vertlistf.Count -1 do
      output.Add(vertlistf[i]);
      for j := 0 to blobsworth.Count -1 do
      output.Add('3' + ' ' + blobsworth[j]);

      eightblobsl.Free;
      hopper1.Free;
      wooda.Free;
      finalindex.Free;
      blobsworth.Free;
      vertlistf.Free;

      Label5.Caption := 'Conversion complete ' ;
      Application.ProcessMessages;
      Timer1StopTimer(Sender);
      vtkout := false;
      plyout := true;


end;


{******************************************************************************
4444444444444444444444444444444444444444444444444444444444444444444444444444444
*******************************************************************************
 old old   old            old old old            old old old old old}



function TForm1.GetToken(aString, SepChar: string; TokenNum: Byte): string;
var
  Token: string;
  StrLen: Integer;
  Num: Integer;
  EndofToken: Integer;
begin
  StrLen := Length(aString);
  Num := 1;
  EndofToken := StrLen;
  while ((Num <= TokenNum) and (EndofToken <> 0)) do
  begin
    EndofToken := Pos(SepChar, aString);
    if EndofToken <> 0 then
    begin
      Token := Copy(aString, 1, EndofToken - 1);
      Delete(aString, 1, EndofToken);
      Inc(Num);
    end
    else
      Token := aString;
  end;
  if Num >= TokenNum then
    Result := Token
  else
    Result := '';
end;

function TForm1.Anglesep(x1, y1, z1, x2, y2, z2: Double): double;
var
  leng1, leng2, costheta, angle: Double;
begin
         {recall the dot product
          a⋅b=∥a∥∥b∥cosθ where  theta separates a and b.
          cos θ = (AxBx + AyBy + AzBz) / |A||B|  }
  leng1 := Sqrt((x1 * x1) + (y1 * y1) + (z1 * z1));
  leng2 := Sqrt((x2 * x2) + (y2 * y2) + (z2 * z2));
  if (Abs(leng1 * leng2) <> 0) then begin
  costheta := ((x1 * x2) + (y1 * y2) + (z1 * z2)) / (leng1 * leng2);

  if Abs(costheta) <= 1 then
  angle := RadtoDeg(ArcCos(costheta));
  end
  else angle := 0;

  Result := angle;
end;

function TForm1.GetWinding(i1, i2, i3, i4 : String): integer;
var
  i1x, i1y, i1z, i2x, i2y, i2z, i3x, i3y, i3z, i4x, i4y, i4z, tvecx,
  tvecy, tvecz, p1x, p1y, p1z, p2x, p2y, p2z, wpx, wpy, wpz, wdp: Double;
begin
  i1x := Numarrayx[StrtoInt(i1)];
  i1y := Numarrayy[StrtoInt(i1)];
  i1z := Numarrayz[StrtoInt(i1)];
  i2x := Numarrayx[StrtoInt(i2)];
  i2y := Numarrayy[StrtoInt(i2)];
  i2z := Numarrayz[StrtoInt(i2)];
  i3x := Numarrayx[StrtoInt(i3)];
  i3y := Numarrayy[StrtoInt(i3)];
  i3z := Numarrayz[StrtoInt(i3)];
  i4x := Numarrayx[StrtoInt(i4)];
  i4y := Numarrayy[StrtoInt(i4)];
  i4z := Numarrayz[StrtoInt(i4)];

  tvecx := i4x -i1x;
  tvecy := i4y -i1y;
  tvecz := i4z -i1z;
  p1x := i1x -i2x;
  p1y := i1y -i2y;
  p1z := i1z -i2z;
  p2x := i1x -i3x;
  p2y := i1y -i3y;
  p2z := i1z -i3z;


   {============================================================
      cross product AxB = (a2b3 - a3b2, a3b1 - a1b3, a1b2 - a2b1)
      dot product AxB = (a1*b1 + a2*b2 + a3*b3)
      ============================================================  }

  wpx := (p1y * p2z) - (p1z * p2y);
  wpy := (p1z * p2x) - (p1x * p2z);
  wpz := (p1x * p2y) - (p1y * p2x);

  wdp := (tvecx * wpx) + (tvecy * wpy) + (tvecz * wpz);

  if wdp < 0 then Result := -1
  else Result := 1;

  end;

function TForm1.FindEdgeSite(s1, s2, s3, s4, s5, s6 : String): string;
var out1, out2 : String;
begin
      begin {1}
      if s3 = s1 then
      if s5 = s2 then
      out1 := s4;
      end;

      begin {2}
      if s4 = s1 then
      if s6 = s2 then
      out1 := s5;
      end;

      begin {3}
      if s6 = s1 then
      if s4 = s2 then
      out1 := s3;
      end;

      begin {4}
      if s5 = s1 then
      if s3 = s2 then
      out1 := s6;
      end;

      begin {5}
      if s6 = s1 then
      if s3 = s2 then
      out1 := s5;
      end;

      begin {6}
      if s3 = s1 then
      if s4 = s2 then
      out1 := s6;
      end;

      begin {7}
      if s4 = s1 then
      if s5 = s2 then
      out1 := s3;
      end;

      begin  {8}
      if s5 = s1 then
      if s6 = s2 then
      out1 := s4;
      end;

      begin  {9}
      if s6 = s1 then
      if s5 = s2 then
      out1 := s3;
      end;

      begin  {10}
      if s5 = s1 then
      if s4 = s2 then
      out1 := s6;
      end;

      begin  {11}
      if s4 = s1 then
      if s3 = s2 then
      out1 := s5;
      end;

      begin  {12}
      if s3 = s1 then
      if s6 = s2 then
      out1 := s4;
      end;

      if s3 <> s1 then begin
      if s3 <> s2 then begin
      if s3 <> out1 then begin
      out2 := s3;
      end;
      end;
      end;

      if s4 <> s1 then begin
      if s4 <> s2 then begin
      if s4 <> out1 then begin
      out2 := s4;
      end;
      end;
      end;

      if s5 <> s1 then begin
      if s5 <> s2 then begin
      if s5 <> out1 then begin
      out2 := s5;
      end;
      end;
      end;

      if s6 <> s1 then begin
      if s6 <> s2 then begin
      if s6 <> out1 then begin
      out2 := s6;
      end;
      end;
      end;

      Result := out1 + ',' + out2;
end;

function TForm1.CheckVol(i1, i2, i3, i4 : Integer) : Double;

var
  i1x, i1y, i1z, i2x, i2y, i2z, i3x, i3y, i3z, i4x, i4y, i4z, tvecx,
  tvecy, tvecz, p1x, p1y, p1z, p2x, p2y, p2z, wpx, wpy, wpz, wdp, l1, l2,
  l3, volp: Double;
begin
  i1x := Numarrayx[i1];
  i1y := Numarrayy[i1];
  i1z := Numarrayz[i1];
  i2x := Numarrayx[i2];
  i2y := Numarrayy[i2];
  i2z := Numarrayz[i2];
  i3x := Numarrayx[i3];
  i3y := Numarrayy[i3];
  i3z := Numarrayz[i3];
  i4x := Numarrayx[i4];
  i4y := Numarrayy[i4];
  i4z := Numarrayz[i4];

  tvecx := i4x -i1x;
  tvecy := i4y -i1y;
  tvecz := i4z -i1z;
  p1x := i1x -i2x;
  p1y := i1y -i2y;
  p1z := i1z -i2z;
  p2x := i1x -i3x;
  p2y := i1y -i3y;
  p2z := i1z -i3z;
  l1 := sqrt(sqr(tvecx) + sqr(tvecy) + sqr(tvecz));
  l2 := sqrt(sqr(p1x) + sqr(p1y) + sqr(p1z));
  l3 := sqrt(sqr(p2x) + sqr(p2y) + sqr(p2z));
  volp := l1 * l2 * l3;

   {============================================================
      cross product AxB = (a2b3 - a3b2, a3b1 - a1b3, a1b2 - a2b1)
      dot product AxB = (a1*b1 + a2*b2 + a3*b3)
      ============================================================  }

  wpx := (p1y * p2z) - (p1z * p2y);
  wpy := (p1z * p2x) - (p1x * p2z);
  wpz := (p1x * p2y) - (p1y * p2x);

  wdp := (tvecx * wpx) + (tvecy * wpy) + (tvecz * wpz);

  if volp <> 0 then Result := Abs(wdp) / volp
  else Result := 0;

end;

procedure TForm1.EnforceVerdictWinding(Sender: TObject);
var q: Integer;
  tempStr, cr, v0, v1, v2, v6  : String;
  v1x, v1y, v1z, v2x, v2y, v2z, v0x, v0y, v0z, v6x, v6y, v6z,
  w1x, w1y, w1z, w6x, w6y, w6z, w2x, w2y, w2z, du : Double;
begin
   for q := 0 to blobsworth.Count -1 do begin

   tempStr := blobsworth[q];

   v0 := GetToken(tempStr, ' ', 2);
   v1 := GetToken(tempStr, ' ', 3);
   v2 := GetToken(tempStr, ' ', 4);
   v6 := GetToken(tempStr, ' ', 7);

   v0x := (Numarrayx[StrtoInt(v0)]);
   v0y := (Numarrayy[StrtoInt(v0)]);
   v0z := (Numarrayz[StrtoInt(v0)]);
   v1x := (Numarrayx[StrtoInt(v1)]);
   v1y := (Numarrayy[StrtoInt(v1)]);
   v1z := (Numarrayz[StrtoInt(v1)]);
   v2x := (Numarrayx[StrtoInt(v2)]);
   v2y := (Numarrayy[StrtoInt(v2)]);
   v2z := (Numarrayz[StrtoInt(v2)]);
   v6x := (Numarrayx[StrtoInt(v6)]);
   v6y := (Numarrayy[StrtoInt(v6)]);
   v6z := (Numarrayz[StrtoInt(v6)]);

   w1x := v0x -v1x; w1y := v0y - v1y; w1z := v0z -v1z;
   w2x := v2x -v1x; w2y := v2y - v1y; w2z := v2z -v1z;
   w6x := v6x -v1x; w6y := v6y - v1y; w6z := v6z -v1z;
   cr := Crossp(w1x, w1y, w1z, w2x, w2y, w2z);

   du := Dotp(StrtoFloat(GetToken(cr, ' ', 1)),
     StrtoFloat(GetToken(cr, ' ', 2)), StrtoFloat(GetToken(cr, ' ', 3)), w6x, w6y, w6z);

    { output.Add('v0,v1,v2,v6 '+(v0)+' '+(v1)+' '+(v2)+' '+(v6));
     output.Add('v0x,v0y,v0z ' +FloattoStr(v0x)+' '+FloattoStr(v0y)+' '+FloattoStr(v0z));
     output.Add('v1x,v1y,v1z ' +FloattoStr(v1x)+' '+FloattoStr(v1y)+' '+FloattoStr(v1z));
     output.Add('v2x,v2y,v2z ' +FloattoStr(v2x)+' '+FloattoStr(v2y)+' '+FloattoStr(v2z));
     output.Add('v6x,v6y,v6z ' +FloattoStr(v6x)+' '+FloattoStr(v6y)+' '+FloattoStr(v6z));
     output.Add('du ' + FloattoStr(du));     }

     {*******************************************
     Note: I don't know where the winding gets done in Blenbridge, or whether
     it is inherited from the Blender .ply export. Anyway, if the leading face
     in the blobsworth line gives a positive du, that means the face is wound
     ccw, and needs to be changed. When blobsworth is reached, the minimum
     number of elements remain (after sorting), so it seems that is a good place
     to check the winding.}

  if du > 0 then begin
    blobsworth[q] := ' ' + GetToken(tempStr, ' ', 6) + ' ' + GetToken(tempStr, ' ', 7) +
     ' ' +  GetToken(tempStr, ' ', 8) + ' ' + GetToken(tempStr, ' ', 9) + ' ' +
     GetToken(tempStr, ' ', 2) + ' ' + GetToken(tempStr, ' ', 3) + ' ' +
     GetToken(tempStr, ' ', 4) + ' ' + GetToken(tempStr, ' ', 5);

    end;
  {else if du < 0 then begin
    blobsworth[q] := ' ' + GetToken(tempStr, ' ', 6) + ' ' + GetToken(tempStr, ' ', 7) +
     ' ' +  GetToken(tempStr, ' ', 8) + ' ' + GetToken(tempStr, ' ', 9) + ' ' +
     GetToken(tempStr, ' ', 2) + ' ' + GetToken(tempStr, ' ', 3) + ' ' +
     GetToken(tempStr, ' ', 4) + ' ' + GetToken(tempStr, ' ', 5);
    end; }


 end;
end;

function TForm1.Crossp(w1, w2, w3, x1, x2, x3: Double): String;
{the cross product, with the coordinates of two vectors as input}
var out1, out2, out3: Double;
begin

   out1 :=  (w2 * x3) -(w3 * x2);
   out2 :=  (w3 * x1) -(w1 * x3);
   out3 :=  (w1 * x2) -(w2 * x1);

   Result := FloattoStr(out1) + ' ' + FloattoStr(out2) + ' ' +
   FloattoStr(out3);
end;

function TForm1.Dotp(y1, y2, y3, z1, z2, z3: Double): Double;
{the dot product, with the coordinates of two vectors as input}
var out1 : Double;
begin
    out1 := (y1 * z1) + (y2 * z2) +  (y3 * z3);

    Result := out1;
end;



end.
