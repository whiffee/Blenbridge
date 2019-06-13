{  Blenbridge version 1.18
   written by Gary Bollenbach
   September 11, 2018


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
  MaskEdit, ExtCtrls, Math, IniFiles, SynEdit;

type

  { TForm1 }

  TForm1 = class(TForm)
    Button1: TButton;
    Button2: TButton;
    Button3: TButton;
    Button4: TButton;
    Button5: TButton;
    Button6: TButton;
    Button7: TButton;
    Button8: TButton;
    CheckBox1: TCheckBox;
    Label1: TLabel;
    Label2: TLabel;
    Label3: TLabel;
    Label4: TLabel;
    Label5: TLabel;
    Label6: TLabel;
    ListBox1: TListBox;
    MaskEdit1: TMaskEdit;
    MaskEdit2: TMaskEdit;
    OpenDialog1: TOpenDialog;
    SaveDialog1: TSaveDialog;
    SynEdit1: TSynEdit;
    Timer1: TTimer;
    procedure Button1Click(Sender: TObject);
    procedure Button2Click(Sender: TObject);
    procedure Button3Click(Sender: TObject);
    procedure Button4Click(Sender: TObject);
    procedure Button5Click(Sender: TObject);
    procedure Button6Click(Sender: TObject);
    procedure Button7Click(Sender: TObject);
    procedure Button8Click(Sender: TObject);
    procedure FormDestroy(Sender: TObject);
    procedure FormShow(Sender: TObject);
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

  private
    { private declarations }
  public
    { public declarations }
    mycurrentDir2, myvar3, myvar4, a1adj, a2adj, a3adj, a4adj : string;
    numberofverts, numberoffaces, normalno, numberofcells, radfac,
     ElapsedT, close1, F3, F, eightblobscounter, tbp : Integer;
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
    separray, septemp, copa, m1 : array [0..100] of Double;
    {m1 is the array for objects: form, memo, button, label, checkbox, mask edit:
    fm1, m1, m3, b1, b2, b3, b4, b5, b6,
    la1, la2, la3, la4, cb1, me1, and the attributes H, W, L, T }
    fc : array [0..4] of Double;
    formsyze, inivaluef : Single;

  end;

var
  Form1: TForm1;

implementation

{$R *.lfm}

{ TForm1 }

procedure TForm1.Button1Click(Sender: TObject);
{var
slash : Integer;  }

begin
  Label5.visible := false;
 if opendialog1.execute then
    begin
    myvar3:= opendialog1.filename;
    SynEdit1.lines.LoadFromFile(myvar3);
    end;

    Listbox1.Items.Add(myvar3);
 {  slash := 0; }
end;

procedure TForm1.Button2Click(Sender: TObject);
begin
   if myvar3 <> '' then begin
   Label5.visible := true;
   Label5.Caption := 'Initializing ' ;
   Application.ProcessMessages;
   PlyWriteVtk(Sender);
   end;

end;

procedure TForm1.Button3Click(Sender: TObject);

begin
   Label5.visible := false;
   savedialog1.FileName := myvar3;
   if savedialog1.execute then
    begin
    myvar4 := savedialog1.filename;
    output.SaveToFile(myvar4);
  end;
end;

procedure TForm1.Button4Click(Sender: TObject);
begin

  {Application.terminate;
  while not Application.Terminated do
  Application.ProcessMessages;}
   FormDestroy(Sender);
end;

procedure TForm1.Button5Click(Sender: TObject);
var
  pic : Double;
begin
  {f}m1[0] := 474; m1[1] := 640; {se1}m1[2] := 296; m1[3] := 600;
  m1[4] := 24; m1[5] := 144; m1[6] := 8;{m3}m1[12] := 48 ; m1[13] := 432;
  m1[14] := 186; m1[15] := 72; m1[16] := 8; {b1}m1[17] := 25;
  m1[18] := 82; m1[19] := 24; m1[20] := 32;
 {b2}m1[21] := 25; m1[22] := 42; m1[23] := 124; m1[24] := 32;
  {b3}m1[25] := 25; m1[26] := 82; m1[27] := 244;
  m1[28] := 32; {b4}m1[29] := 25; m1[30] := 82; m1[31] := 344;
  m1[32] := 32; {b5}m1[33] := 25; m1[34] := 90; m1[35] := 444;
  m1[36] := 32; {b6}m1[37] := 25; m1[38] := 42;
  m1[39] := 184; m1[40] := 32; {la5}m1[45] := 24; m1[46] := 540;
  m1[47] := 18; m1[48] := 0;{la2}m1[49] := 34; m1[50] := 31;
  m1[51] := 24; m1[52] := 96;{cb1}m1[53] := 21 ; m1[54] := 21;
  m1[55] := 24; m1[56] := 72;{me1}m1[57] := 22; m1[58] := 40;
  m1[59] := 61; m1[60] := 72;{la3}m1[61] := 17; m1[62] := 45;
  m1[63] := 62; m1[64] := 104;{la4}m1[65] := 24; m1[66] := 574;
  m1[67] := 0; m1[68] := 450;{me2}m1[69] := 22; m1[70] := 60;
  m1[71] := 116; m1[72] := 72;{la6}m1[73] := 17; m1[74] := 50;
  m1[75] := 125; m1[76] := 104;{b7}m1[77] := 12; m1[78] := 15;
  m1[79] := 575; m1[80] := 47;{b8}m1[81] := 12; m1[82] := 15;
  m1[83] := 590; m1[84] := 47;{la1}m1[85] := 14; m1[86] := 60;
  m1[87] := 568; m1[88] := 33;

  {fc[0] := 0.7; fc[1] := 0.85; fc[2] := 1.0; fc[3] := 1.25; fc[4] := 1.5; }
  fc[0] := 1.1; fc[1] := 1.3; fc[2] := 1.5; fc[3] := 1.7; fc[4] := 1.9;

  if Button5.Caption = 'Size 3' then begin
  Button5.Caption := 'Size 4';
  pic := fc[3];
  formsyze := 4.0;
  end
  else
  if Button5.Caption = 'Size 4' then begin
  Button5.Caption := 'Size 5';
  pic := fc[4];
  formsyze := 5.0;
  end
  else
  if Button5.Caption = 'Size 5' then begin
  Button5.Caption := 'Size 1';
  pic := fc[0];
  formsyze := 1.0;
  end
  else
  if Button5.Caption = 'Size 1' then begin
  Button5.Caption := 'Size 2';
  pic := fc[1];
  formsyze := 2.0;
  end
  else
  if Button5.Caption = 'Size 2' then begin
  Button5.Caption := 'Size 3';
  pic := fc[2];
  formsyze := 3.0;
  end ;

  begin
  Form1.Height := Round(pic * m1[0]); Form1.Width := Round(pic * m1[1]);
  SynEdit1.Height := Round(pic * m1[2]); SynEdit1.Width := Round(pic * m1[3]);
  SynEdit1.Left := Round(pic * m1[4]); SynEdit1.Top := Round(pic * m1[5]);
  ListBox1.Height := Round(pic * m1[12]); ListBox1.Width := Round(pic * m1[13]);
  ListBox1.Left := Round(pic * m1[14]); ListBox1.Top := Round(pic * m1[15]);
  Button1.Height := Round(pic * m1[17]); Button1.Width := Round(pic * m1[18]);
  Button1.Left := Round(pic * m1[19]); Button1.Top := Round(pic * m1[20]);
  Button2.Height := Round(pic * m1[21]); Button2.Width := Round(pic * m1[22]);
  Button2.Left := Round(pic * m1[23]); Button2.Top := Round(pic * m1[24]);
  Button3.Height := Round(pic * m1[25]); Button3.Width := Round(pic * m1[26]);
  Button3.Left := Round(pic * m1[27]); Button3.Top := Round(pic * m1[28]);
  Button4.Height := Round(pic * m1[29]); Button4.Width := Round(pic * m1[30]);
  Button4.Left := Round(pic * m1[31]); Button4.Top := Round(pic * m1[32]);
  Button5.Height := Round(pic * m1[33]); Button5.Width := Round(pic * m1[34]);
  Button5.Left := Round(pic * m1[35]); Button5.Top := Round(pic * m1[36]);
  Button6.Height := Round(pic * m1[37]); Button6.Width := Round(pic * m1[38]);
  Button6.Left := Round(pic * m1[39]); Button6.Top := Round(pic * m1[40]);
  Label5.Height := Round(pic * m1[45]); Label5.Width := Round(pic * m1[46]);
  Label5.Left := Round(pic * m1[47]); Label5.Top := Round(pic * m1[48]);
  Label2.Height := Round(pic * m1[49]); Label2.Width := Round(pic * m1[50]);
  Label2.Left := Round(pic * m1[51]); Label2.Top := Round(pic * m1[52]);
  CheckBox1.Height := Round(pic * m1[53]); CheckBox1.Width := Round(pic * m1[54]);
  CheckBox1.Left := Round(pic * m1[55]); CheckBox1.Top := Round(pic * m1[56]);
  MaskEdit1.Height := Round(pic * m1[57]); MaskEdit1.Width := Round(pic * m1[58]);
  MaskEdit1.Left := Round(pic * m1[59]); MaskEdit1.Top := Round(pic * m1[60]);
  Label3.Height := Round(pic * m1[61]); Label3.Width := Round(pic * m1[62]);
  Label3.Left := Round(pic * m1[63]); Label3.Top := Round(pic * m1[64]);
  Label4.Height := Round(pic * m1[65]); Label4.Width := Round(pic * m1[66]);
  Label4.Left := Round(pic * m1[67]); Label4.Top := Round(pic * m1[68]);
  MaskEdit2.Height := Round(pic * m1[69]); MaskEdit2.Width := Round(pic * m1[70]);
  MaskEdit2.Left := Round(pic * m1[71]); MaskEdit2.Top := Round(pic * m1[72]);
  Label6.Height := Round(pic * m1[73]); Label6.Width := Round(pic * m1[74]);
  Label6.Left := Round(pic * m1[75]); Label6.Top := Round(pic * m1[76]);
  Button7.Height := Round(pic * m1[77]); Button7.Width := Round(pic * m1[78]);
  Button7.Left := Round(pic * m1[79]); Button7.Top := Round(pic * m1[80]);
  Button8.Height := Round(pic * m1[81]); Button8.Width := Round(pic * m1[82]);
  Button8.Left := Round(pic * m1[83]); Button8.Top := Round(pic * m1[84]);
  Label1.Height := Round(pic * m1[85]); Label1.Width := Round(pic * m1[86]);
  Label1.Left := Round(pic * m1[87]); Label1.Top := Round(pic * m1[88]);

  SynEdit1.Font.Size := Round(pic * 6); ListBox1.Font.Size := Round(pic * 6);
  Button1.Font.Size := Round(pic * 7); Button2.Font.Size := Round(pic * 7);
  Button3.Font.Size := Round(pic * 7); Button4.Font.Size := Round(pic * 7);
  Button5.Font.Size := Round(pic * 7); Button6.Font.Size := Round(pic * 7);
  Label5.Font.Size := Round(pic * 6); Label2.Font.Size := Round(pic * 6);
  Label3.Font.Size := Round(pic * 6); MaskEdit1.Font.Size := Round(pic * 6);
  Label4.Font.Size := Round(pic * 6);MaskEdit2.Font.Size := Round(pic * 6);
  Label6.Font.Size := Round(pic * 6);Button7.Font.Size := Round(pic * 6);
  Button8.Font.Size := Round(pic * 4);Label1.Font.Size := Round(pic * 3.5);
  end;
end;

procedure TForm1.AdjustFont(Sender: TObject);
var a : Integer;
begin
  SynEdit1.Font.Size := SynEdit1.Font.Size  + tbp; Listbox1.Font.Size := ListBox1.Font.Size + tbp;
  Button1.Font.Size := Button1.Font.Size  + tbp; Button2.Font.Size := Button2.Font.Size + tbp;
  Button3.Font.Size := Button3.Font.Size  + tbp; Button4.Font.Size := Button4.Font.Size + tbp;
  Button5.Font.Size := Button5.Font.Size  + tbp; Button6.Font.Size := Button6.Font.Size + tbp;
  Label5.Font.Size := Label5.Font.Size  + tbp; Label2.Font.Size := Label2.Font.Size + tbp;
  Label3.Font.Size := Label3.Font.Size  + tbp; MaskEdit1.Font.Size := MaskEdit1.Font.Size + tbp;
  Label4.Font.Size := Label4.Font.Size + tbp;MaskEdit2.Font.Size := MaskEdit2.Font.Size + tbp;
  Label6.Font.Size := Label6.Font.Size + tbp;Button7.Font.Size := Button7.Font.Size + tbp;
  Button8.Font.Size := Button8.Font.Size + tbp;Label1.Font.Size := Label1.Font.Size + tbp;
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

procedure TForm1.FormDestroy(Sender: TObject);
var
    myINI : TINIFile;
begin
   myINI := TINIFile.Create(ExtractFilePath(Application.EXEName) +
   'blenbridge.ini');

   with myINI do begin
      WriteFloat('Settings','Form Size', formsyze);
   end;
   myINI.Free;
   close1 := close1 +1;
  { Button4.Color := clYellow;
   Button4.Color := $007E6E09; }
   Button4.Color := RGBToColor(255, 251, 148);
   Button4.Font.Style := [fsBold];
   Button4.Caption := 'Quit?';
   if close1 = 2 then begin
   Halt(0);
   end;
end;

procedure TForm1.FormShow(Sender: TObject);
var
myINI : TINIFile;
begin
  Label5.Font.Color := clGreen;
  Timer1.enabled := false;
  close1 := 0;

  myINI := TINIFile.Create(ExtractFilePath(Application.EXEName) +
  'blenbridge.ini');

    inivaluef := myINI.ReadFloat('Settings','Form Size', 3.0);

    if inivaluef = 2.0 then Button5.Caption := 'Size 1';
    if inivaluef = 3.0 then Button5.Caption := 'Size 2';
    if inivaluef = 4.0 then Button5.Caption := 'Size 3';
    if inivaluef = 5.0 then Button5.Caption := 'Size 4';
    if inivaluef = 1.0 then Button5.Caption := 'Size 5';

    myINI.Free;
    Button5Click(Sender);
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
   output.Add('# created by Blenbridge 1.18: add *.vtk* by hand');
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
  { charz,} a1, a2, a3, a4, FES, flst, flsb, topkey, bottomkey{, tempT2}: String;
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

      {chk
      output.Add( ' ');
      output.Add('vertlistf[' + InttoStr(i) + '] .' + vertlistf[i] + '.');
      for s := 0 to Trigarray.Count -1 do
      output.Add('Trigarray[' + InttoStr(s) + '] .' + Trigarray[s] + '.');
      output.Add('a1= .' + a1 + '. a2= .' + a2 + '.');
      output.Add('a3= .' + a3 + '. a4= .' + a4 + '.');
      chk}

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

      {chk
      output.Add( 'a1adj a1 a4 = '  + a1adj + ' ' + a1 + ' ' + a4);
      output.Add( 'a2adj a2 a3 = '  + a2adj + ' ' + a2 + ' ' + a3);
      output.Add('flst = .' + flst + '.');
      output.Add('flsb = .' + flsb + '.');
      output.Add('topkey bottomkey .' + topkey + '. .' + bottomkey + '.');
      chk}

      {The block below double-checks to make sure the prospective keystone
      face is present in luniverse. This may not be necessary, but it
      is a nod to Murphy's Law. Note: both coppa and copvol represent
      volumes, but a reasonable relation factor to use is a guess and subject
      to change.}

     { for e := 0 to luniverse.Count -1 do begin
      if (AnsiPos(' ' + a1adj + ' ', luniverse[e]) <> 0) then
      if (AnsiPos(' ' + a1 + ' ', luniverse[e]) <> 0) then
      if (AnsiPos(' ' + a4 + ' ', luniverse[e]) <> 0) then
      if (AnsiPos(' ' + topkey + ' ', luniverse[e]) <> 0) then }
      if Abs(coppa) > comvol * copvol then begin
      writeit := true;
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

      EnforceVerdictWinding(Sender);

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

    if CheckBox1.Checked = true then begin

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
   a3int, a2int, otherone, closure, g : Integer;
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
      chk }

      for b := 0 to luniverse.Count -1 do begin
      if (AnsiPos(' ' + a2 + ' ', luniverse[b]) <> 0) then
      if (AnsiPos(' ' + a3 + ' ', luniverse[b])<> 0) then
      if luniverse[b] <> vertlistf[i] then begin
      oneedge.Add(luniverse[b]);
      end;
      end;
     { for g := 0 to oneedge.Count -1 do
      output.Add('oneedge[' + InttoStr(g) + '] ' + oneedge[g]); }

      for c := 0 to luniverse.Count -1 do begin
      if (AnsiPos(' ' + a3 + ' ', luniverse[c]) <> 0) then
      if (AnsiPos(' ' + a1 + ' ', luniverse[c])<> 0) then
      if luniverse[c] <> vertlistf[i] then begin
      twoedge.Add(luniverse[c]);
      end;
      end;
     { for g := 0 to twoedge.Count -1 do
      output.Add('twoedge[' + InttoStr(g) + '] ' + twoedge[g]);  }

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

    {   for w := 0 to eightblobs3.Count -1 do
        eightblobs[w] := (eightblobs3[w]);
      for i := 0 to eightblobs3.Count -1 do
      output.Add('****eightblobs ' + InttoStr(i) + ' ' + eightblobs[i]);}
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

   else Label5.Caption := 'Path choice error line 1829';
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

      eightblobsl.Free;
      hopper1.Free;
      wooda.Free;
      finalindex.Free;
      blobsworth.Free;
      vertlistf.Free;

      Label5.Caption := 'Conversion complete ' ;
      Application.ProcessMessages;
      Timer1StopTimer(Sender);


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
  tempStr, cr  : String;
  v1x, v1y, v1z, v2x, v2y, v2z, v3x, v3y, v3z, v6x, v6y, v6z,
  w1x, w1y, w1z, w2x, w2y, w2z, upsubx, upsuby, upsubz,
  upsubnorm, w8norm, du, dur, numer, normcrx, normcry, normcrz,
  locv6x, locv6y, locv6z, normlocv : Double;
begin
   for q := 0 to numberofcells -1 do begin
   tempStr := eightblobsf[q];
   v1x := StrtoFloat(GetToken(vertlistf[StrtoInt(GetToken(tempStr, ' ', 1))], ' ', 1));
   v1y := StrtoFloat(GetToken(vertlistf[StrtoInt(GetToken(tempStr, ' ', 1))], ' ', 2));
   v1z := StrtoFloat(GetToken(vertlistf[StrtoInt(GetToken(tempStr, ' ', 1))], ' ', 3));
   v2x := StrtoFloat(GetToken(vertlistf[StrtoInt(GetToken(tempStr, ' ', 2))], ' ', 1));
   v2y := StrtoFloat(GetToken(vertlistf[StrtoInt(GetToken(tempStr, ' ', 2))], ' ', 2));
   v2z := StrtoFloat(GetToken(vertlistf[StrtoInt(GetToken(tempStr, ' ', 2))], ' ', 3));
   v3x := StrtoFloat(GetToken(vertlistf[StrtoInt(GetToken(tempStr, ' ', 3))], ' ', 1));
   v3y := StrtoFloat(GetToken(vertlistf[StrtoInt(GetToken(tempStr, ' ', 3))], ' ', 2));
   v3z := StrtoFloat(GetToken(vertlistf[StrtoInt(GetToken(tempStr, ' ', 3))], ' ', 3));
   v6x := StrtoFloat(GetToken(vertlistf[StrtoInt(GetToken(tempStr, ' ', 6))], ' ', 1));
   v6y := StrtoFloat(GetToken(vertlistf[StrtoInt(GetToken(tempStr, ' ', 6))], ' ', 2));
   v6z := StrtoFloat(GetToken(vertlistf[StrtoInt(GetToken(tempStr, ' ', 6))], ' ', 3));

   w1x := v2x -v1x; w1y := v2y - v1y; w1z := v2z -v1z;
   w2x := v2x -v3x; w2y := v2y - v3y; w2z := v2z -v3z;
   {w3x := v6x -v2x; w3y := v6y - v2y; w3z := v6z -v2z; }
   w8norm := sqrt(sqr(v6x) + sqr(v6y) + sqr(v6z));
   cr := Crossp(w1x, w1y, w1z, w2x, w2y, w2z);
   upsubx := StrtoFloat(GetToken(cr, ' ', 1));
   upsuby := StrtoFloat(GetToken(cr, ' ', 2));
   upsubz := StrtoFloat(GetToken(cr, ' ', 3));

   upsubnorm := sqrt(sqr(upsubx) + sqr(upsuby) + sqr(upsubz));
   normcrx := upsubx/upsubnorm;
   normcry := upsuby/upsubnorm;
   normcrz := upsubz/upsubnorm;

   locv6x := v6x -v2x ;
   locv6y := v6y -v2y;
   locv6z := v6z -v2z;
   normlocv := sqrt(sqr(locv6x) + sqr(locv6y) + sqr(locv6z));
   {du := Dotp(w1x, w1y, w1z, StrtoFloat(GetToken(cr, ' ', 1)),
     StrtoFloat(GetToken(cr, ' ', 2)), StrtoFloat(GetToken(cr, ' ', 3)));}
   numer :=(upsubnorm)*(w8norm);
     if numer < 0.0000000000001 then numer := 0.0000000000001;
   { dur := Dotp(upsubx, upsuby, upsubz, v6x, v6y, v6z)/ numer;}
    dur := Dotp(normcrx, normcry, normcrz, locv6x, locv6y, locv6z)/normlocv;

    if dur <= Abs(1) then du := RadtoDeg(Arccos(dur))
    else du := 0;
  { output.Add('upsub ' + FloattoStr(upsubx) + ' ' + FloattoStr(upsuby) + ' ' +
     FloattoStr(upsubz) );
   output.Add('loccrx loccry loccrz ' + FloattoStr(loccrx) + ' ' + FloattoStr(loccry) + ' ' +
     FloattoStr(loccrz) );
   output.Add('v2x v2y v2z ' + FloattoStr(v2x) + ' ' + FloattoStr(v2y) + ' ' +
     FloattoStr(v2z) );
   output.Add('v6x v6y v6z ' + FloattoStr(v6x) + ' ' + FloattoStr(v6y) + ' ' +
     FloattoStr(v6z) );
   output.Add('du ' + FloattoStr(du));
   output.Add('cr ' + cr); }
   {output.Add('normcrx normcry normcrz ' + ' ' + FloattoStr(normcrx) + ' ' +
     FloattoStr(normcry) + ' ' + FloattoStr(normcrz) );}
    { output.Add('loccrx loccry loccrz ' + ' ' + FloattoStr(loccrx) + ' ' +
     FloattoStr(loccry) + ' ' + FloattoStr(loccrz));}
   if du < 90 then begin
   eightblobsf[q] := GetToken(tempStr, ' ', 5) + ' ' + GetToken(tempStr, ' ', 6) +
     ' ' +  GetToken(tempStr, ' ', 7) + ' ' + GetToken(tempStr, ' ', 8) + ' ' +
     GetToken(tempStr, ' ', 1) + ' ' + GetToken(tempStr, ' ', 2) + ' ' +
     GetToken(tempStr, ' ', 3) + ' ' + GetToken(tempStr, ' ', 4);

   end;
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
