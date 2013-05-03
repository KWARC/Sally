package info.kwarc.sissi.model.document.spreadsheet;

import info.kwarc.sally.model.document.spreadsheet.ASMInterface;

import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.OutputStream;

import sally.CellData;
import sally.CellPosition;
import sally.DataParameter;
import sally.FBCreateData;
import sally.IdData;
import sally.IdList;
import sally.LegendCreateData;
import sally.ModelDataMsg;
import sally.RangeData;
import sally.RangeData.Builder;
import sally.SpreadsheetModel;
import sally.StringData;

import com.hp.hpl.jena.rdf.model.Model;

public class IUIPaperData {
	ASMInterface asm;

	public IUIPaperData() {
		asm = new ASMInterface("http://iui-paper");
	}

	IdData createRowFB(int sheet, int startRow, int startCol, String [] content, IdData [] ids) {
		if (content.length == 0) {
			return null;
		}
		return createFB(sheet, startRow, startCol, startRow, startCol+content.length-1, new String[][] {content}, ids);
	}

	IdData createColFB(int sheet, int startRow, int startCol, String [] content, IdData [] ids) {
		if (content.length == 0) {
			return null;
		}
		String [][] c = new String[content.length][1];
		for (int i=0; i<content.length; ++i)
			c[i][0] = content[i];
		return createFB(sheet, startRow, startCol, startRow+content.length-1, startCol, c, ids);
	}

	IdData createFB(int sheet, int startRow, int startCol, int endRow, int endCol, String [][] content, IdData [] ids) {
		FBCreateData.Builder createData = FBCreateData.newBuilder();
		RangeData.Builder range = RangeData.newBuilder();
		for (int i=startRow; i<=endRow; ++i) {
			for (int j=startCol; j<=endCol; ++j) {
				CellData data = CellData.newBuilder().setPosition(sally.CellSpaceInformation.newBuilder().setWidth(1).setHeight(1).setPosition( sally.CellPosition.newBuilder().setSheet(sheet).setCol(j).setRow(i).build()).build()).setValue(content[i-startRow][j-startCol]).build();
				range.addCells(data);
			}
		}
		createData.setRange(range.build());
		IdList.Builder list = IdList.newBuilder();
		for (IdData data : ids) {
			list.addIds(data);
		}
		createData.setLegends(list.build());
		createData.setParameter(DataParameter.SameContentSameElement);
		return asm.createFB(createData.build());
	}

	// This should be used for header and titles of data
	IdData setHeaderLabel(int sheet, int startRow, int startCol, int length, String text) {
		String [] names = new String[length];
		for (int i=0; i<length; ++i)
			names[i] = text;
		return setRowTableHeaders(sheet, startRow, startCol, names);
	}

	IdData setRowTableHeaders(int sheet, int startRow, int startCol, String [] text) {
		Builder rangeData = RangeData.newBuilder();
		for (int i=0; i<text.length; ++i) {
			CellData data = CellData.newBuilder().setPosition(sally.CellSpaceInformation.newBuilder().setWidth(1).setHeight(1).setPosition( sally.CellPosition.newBuilder().setSheet(sheet).setCol(i+startCol).setRow(startRow).build()).build()).setValue(text[i]).build();
			rangeData.addCells(data);
		}
		return asm.createLegend(LegendCreateData.newBuilder().setFileName("IUI.xls").setItems(rangeData).setParameter(DataParameter.SameContentSameElement).build());
	}

	IdData setColTableHeaders(int sheet, int startRow, int startCol, String [] text) {
		Builder rangeData = RangeData.newBuilder();
		for (int i=0; i<text.length; ++i) {
			CellData data = CellData.newBuilder().setPosition(sally.CellSpaceInformation.newBuilder().setWidth(1).setHeight(1).setPosition( sally.CellPosition.newBuilder().setSheet(sheet).setCol(startCol).setRow(startRow+i).build()).build()).setValue(text[i]).build();
			rangeData.addCells(data);
		}
		return asm.createLegend(LegendCreateData.newBuilder().setFileName("IOI.xls").setItems(rangeData).setParameter(DataParameter.SameContentSameElement).build());
	}

	public void setData() {
		buildVendorA();
		buildComareSheet();
	}
	
	public void buildComareSheet() {
		IdData workSheetid = asm.getWorksheetIDByName(StringData.newBuilder().setName("Pricing").build());

		IdData tableProps = setRowTableHeaders(workSheetid.getId(), 7, 1, new String[] {"Component", "Thread", "Color", "Head", "Type", "Quantity per flange"});

		IdData componentCol = setColTableHeaders(workSheetid.getId(), 8, 1, new String[] {"bolt", "nut", "gasket", "flange", "blind flange"});
		IdData threadCol = setColTableHeaders(workSheetid.getId(), 8, 2, new String[] { "M15", "M15", "_", "M15", "M15"});
		IdData colorCol = setColTableHeaders(workSheetid.getId(), 8, 3, new String[] { "black", "black", "_", "black", "black"});
		IdData headCol = setColTableHeaders(workSheetid.getId(), 8, 4, new String[] { "machine", "_", "_", "_", "_"});
		IdData typeCol = setColTableHeaders(workSheetid.getId(), 8, 5, new String[] { "_", "_", "standard", "_", "_"});
		IdData quantityCol = setColTableHeaders(workSheetid.getId(), 8, 6, new String[] { "6", "6", "1", "1", "1"});

		IdData vendorA = setHeaderLabel(workSheetid.getId(), 5, 7, 2, "Vendor A");
		IdData vendorB = setHeaderLabel(workSheetid.getId(), 5, 9, 2, "Vendor B");
		IdData vendorC = setHeaderLabel(workSheetid.getId(), 5, 11, 2, "Vendor C");
		
		IdData costByPieceVendorA = createColFB(workSheetid.getId(), 8, 7, new String[] {"0.450 EUR", "0.460 EUR", "0.300 EUR", "0.310 EUR", "0.340 EUR"}, new IdData [] {componentCol, threadCol, colorCol, headCol, typeCol, quantityCol, vendorA});
		IdData costTotalVendorA = createColFB(workSheetid.getId(), 8, 8, new String[] {"0.450 EUR", "0.460 EUR", "0.300 EUR", "0.310 EUR", "0.340 EUR"}, new IdData [] {componentCol, threadCol, colorCol, headCol, typeCol, quantityCol, vendorA});
		IdData costByPieceVendorB = createColFB(workSheetid.getId(), 8, 9, new String[] {"0.450 EUR", "0.460 EUR", "0.300 EUR", "0.310 EUR", "0.340 EUR"}, new IdData [] {componentCol, threadCol, colorCol, headCol, typeCol, quantityCol, vendorB});
		IdData costTotalVendorB = createColFB(workSheetid.getId(), 8, 10, new String[] {"0.450 EUR", "0.460 EUR", "0.300 EUR", "0.310 EUR", "0.340 EUR"}, new IdData [] {componentCol, threadCol, colorCol, headCol, typeCol, quantityCol, vendorB});
		IdData costByPieceVendorC = createColFB(workSheetid.getId(), 8, 11, new String[] {"0.450 EUR", "0.460 EUR", "0.300 EUR", "0.310 EUR", "0.340 EUR"}, new IdData [] {componentCol, threadCol, colorCol, headCol, typeCol, quantityCol, vendorC});
		IdData costTotalVendorC = createColFB(workSheetid.getId(), 8, 12, new String[] {"0.450 EUR", "0.460 EUR", "0.300 EUR", "0.310 EUR", "0.340 EUR"}, new IdData [] {componentCol, threadCol, colorCol, headCol, typeCol, quantityCol, vendorC});

		asm.addOntologyLink(componentCol, "https://tnt.kwarc.info/repos/stc/fcad/flange/cds/components.omdoc?component?component");
		asm.addOntologyLink(threadCol, "https://tnt.kwarc.info/repos/stc/fcad/flange/cds/ISOhexthread.omdoc?ISOhexthread?ISOhexthread");
		asm.addOntologyLink(colorCol, "https://tnt.kwarc.info/repos/stc/fcad/flange/cds/colors.omdoc?color?color");
		asm.addOntologyLink(headCol, "https://tnt.kwarc.info/repos/stc/fcad/flange/cds/ISOhexbolt.omdoc?ISOhexbolt?head");
		asm.addOntologyLink(typeCol, "https://tnt.kwarc.info/repos/stc/fcad/flange/cds/comp_types.omdoc?comptype?comptype");
		asm.addOntologyLink(quantityCol, "https://tnt.kwarc.info/repos/stc/fcad/flange/cds/quantity.omdoc?quantity?quantity");

		asm.addOntologyLink(vendorA, "https://tnt.kwarc.info/repos/stc/fcad/flange/cds/vendors.omdoc?vendors?A");
		asm.addOntologyLink(vendorB, "https://tnt.kwarc.info/repos/stc/fcad/flange/cds/vendors.omdoc?vendors?B");
		asm.addOntologyLink(vendorC, "https://tnt.kwarc.info/repos/stc/fcad/flange/cds/vendors.omdoc?vendors?C");
		
		asm.addOntologyLink(costByPieceVendorA, "https://tnt.kwarc.info/repos/stc/fcad/flange/cds/cost.omdoc?cost?bypiece");
		asm.addOntologyLink(costTotalVendorA, "https://tnt.kwarc.info/repos/stc/fcad/flange/cds/cost.omdoc?cost?total");
		asm.addOntologyLink(costByPieceVendorB, "https://tnt.kwarc.info/repos/stc/fcad/flange/cds/cost.omdoc?cost?bypiece");
		asm.addOntologyLink(costTotalVendorB, "https://tnt.kwarc.info/repos/stc/fcad/flange/cds/cost.omdoc?cost?total");
		asm.addOntologyLink(costByPieceVendorC, "https://tnt.kwarc.info/repos/stc/fcad/flange/cds/cost.omdoc?cost?bypiece");
		asm.addOntologyLink(costTotalVendorC, "https://tnt.kwarc.info/repos/stc/fcad/flange/cds/cost.omdoc?cost?total");
		
	}
	
	public void buildVendorA() {
		IdData workSheetid = asm.getWorksheetIDByName(StringData.newBuilder().setName("Vendor A").build());
		
		IdData vendA = setHeaderLabel(workSheetid.getId(), 1, 1, 8, "Price List of Vendor A");
		asm.addOntologyLink(vendA, "http://info.kwarc.sissi.winograd/vendor-A");
		
		
		IdData discountMinQuantity = setRowTableHeaders(workSheetid.getId(), 4, 1, new String[] {"100", "1000", "10000", ">10000"} );
		IdData discountRatesFB = createRowFB(workSheetid.getId(), 5, 1, new String[] {"100.000%", "99.000%", "95.000%", "90.000%"}, new IdData [] {vendA, discountMinQuantity});
		asm.addOntologyLink(discountMinQuantity, "http://info.kwarc.sissi.winograd/discount-min-quantities");
		asm.addOntologyLink(discountRatesFB, "http://info.kwarc.sissi.winograd/discount-rates");
		
		IdData tableProps = setRowTableHeaders(workSheetid.getId(), 7, 1, new String[] {"Component", "Thread", "Color", "Head", "Type", "Basic Price"});

		IdData componentCol = setColTableHeaders(workSheetid.getId(), 8, 1, new String[] {"bolt", "bolt", "bolt", "bolt", "bolt", "bolt", "bolt", "bolt", "nut", "nut", "gasket", "flange", "flange", "flange", "blind flange", "blind flange", "blind flange" });
		IdData threadCol = setColTableHeaders(workSheetid.getId(), 8, 2, new String[] { "M15", "M15", "M15", "M15", "M15", "M15", "M16", "M16", "M15", "M16", "_", "M15", "M15", "M16", "M15", "M16", "M17"});
		IdData colorCol = setColTableHeaders(workSheetid.getId(), 8, 3, new String[] { "silver", "silver", "black", "silver", "red", "black", "black", "black", "black", "black", "_", "black", "silver", "black", "black", "black", "black"});
		IdData headCol = setColTableHeaders(workSheetid.getId(), 8, 4, new String[] { "carriage", "stove", "machine", "machine", "machine", "machine", "machine", "machine", "_", "_", "_", "_", "_", "_", "_", "_", "_" });
		IdData typeCol = setColTableHeaders(workSheetid.getId(), 8, 5, new String[] { "_", "_", "_", "_", "_", "_", "_", "_", "_", "_", "standard", "_", "_", "_", "_", "_", "_"});

		IdData cost = createColFB(workSheetid.getId(), 8, 6, new String[] {"0.450 EUR", "0.460 EUR", "0.300 EUR", "0.310 EUR", "0.340 EUR", "0.350 EUR", "0.300 EUR", "0.350 EUR", "0.504 EUR", "0.498 EUR", "2.040 EUR", "1.080 EUR", "1.080 EUR", "1.090 EUR", "0.888 EUR", "0.888 EUR", "0.888 EUR"}, new IdData [] {componentCol, threadCol, colorCol, headCol, typeCol});
		
		asm.addOntologyLink(componentCol, "https://tnt.kwarc.info/repos/stc/fcad/flange/cds/ISOhexbolt.omdoc?ISOhexbolt?ISOhexbolt");
		asm.addOntologyLink(threadCol, "https://tnt.kwarc.info/repos/stc/fcad/flange/cds/ISOhexthread.omdoc?ISOhexthread?ISOhexthread");
		asm.addOntologyLink(colorCol, "https://tnt.kwarc.info/repos/stc/fcad/flange/cds/colors.omdoc?color?color");
		asm.addOntologyLink(headCol, "https://tnt.kwarc.info/repos/stc/fcad/flange/cds/ISOhexbolt.omdoc?ISOhexbolt?head");
		asm.addOntologyLink(typeCol, "https://tnt.kwarc.info/repos/stc/fcad/flange/cds/comp_types.omdoc?comptype?comptype");
		asm.addOntologyLink(cost, "https://tnt.kwarc.info/repos/stc/fcad/flange/cds/cost.omdoc?cost?cost");
	}

	public void writeRDF() {
		OutputStream file;
		try {
			file = new FileOutputStream("iui-model.rdf");
			asm.getRDFModel().write(file);
			Model model = asm.getRDFModel();
			file.close();
		} catch (FileNotFoundException e) {
			e.printStackTrace();
		} catch (IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
	}

	public void writeProto() {
		OutputStream file;
		try {
			file = new FileOutputStream("iui-model.bin");
			SpreadsheetModel model = getAsm().serialize();
			model.writeTo(file);
		} catch (FileNotFoundException e) {
			e.printStackTrace();
		} catch (IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
	}

	public ASMInterface getAsm() {
		return asm;
	}
	
	public Model getModel() {
		return asm.getRDFModel();
	}
	
	public static void main(String[] args) {
		IUIPaperData t = new IUIPaperData();
		
		t.setData();
		t.writeRDF();
		t.writeProto();
		
		IdData workSheetid = t.getAsm().getWorksheetIDByName(StringData.newBuilder().setName("Vendor A").build());
		System.out.println(t.getAsm().getOntologyForPosition(CellPosition.newBuilder().setSheet(workSheetid.getId()).setRow(8).setCol(2).build()));
	}
}
