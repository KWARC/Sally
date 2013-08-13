package info.kwarc.sissi.model.document.spreadsheet;

import info.kwarc.sally.model.document.spreadsheet.ASMInterface;

import java.io.ByteArrayOutputStream;
import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.OutputStream;
import java.util.Arrays;
import java.util.List;

import org.apache.commons.codec.binary.Base64;

import sally.CellData;
import sally.CellPosition;
import sally.DataParameter;
import sally.FBCreateData;
import sally.LegendCreateData;
import sally.RangeData;
import sally.RangeData.Builder;
import sally.SpreadsheetModel;

import com.hp.hpl.jena.rdf.model.Model;

public class IUIPaperData {
	ASMInterface asm;

	public IUIPaperData() {
		asm = new ASMInterface("http://iui-paper");
	}

	Integer createRowFB(int sheet, int startRow, int startCol, String [] content, Integer [] ids) {
		if (content.length == 0) {
			return null;
		}
		return createFB(sheet, startRow, startCol, startRow, startCol+content.length-1, new String[][] {content}, ids);
	}

	Integer createColFB(int sheet, int startRow, int startCol, String [] content, Integer [] ids) {
		if (content.length == 0) {
			return null;
		}
		String [][] c = new String[content.length][1];
		for (int i=0; i<content.length; ++i)
			c[i][0] = content[i];
		return createFB(sheet, startRow, startCol, startRow+content.length-1, startCol, c, ids);
	}

	Integer createFB(int sheet, int startRow, int startCol, int endRow, int endCol, String [][] content, Integer [] ids) {
		startRow--;endRow--;startCol--;endCol--;
		FBCreateData.Builder createData = FBCreateData.newBuilder();
		RangeData.Builder range = RangeData.newBuilder();
		for (int i=startRow; i<=endRow; ++i) {
			for (int j=startCol; j<=endCol; ++j) {
				CellData data = CellData.newBuilder().setPosition(sally.CellSpaceInformation.newBuilder().setWidth(1).setHeight(1).setPosition( sally.CellPosition.newBuilder().setSheet(sheet).setCol(j).setRow(i).build()).build()).setValue(content[i-startRow][j-startCol]).build();
				range.addCells(data);
			}
		}
		createData.setRange(range.build());
		List<Integer> list = Arrays.asList(ids); 
		createData.addAllLegends(list);
		createData.setParameter(DataParameter.SameContentSameElement);
		return asm.createFB(createData.build());
	}

	// This should be used for header and titles of data
	Integer setHeaderLabel(int sheet, int startRow, int startCol, int length, String text) {
		String [] names = new String[length];
		for (int i=0; i<length; ++i)
			names[i] = text;
		return setRowTableHeaders(sheet, startRow, startCol, names);
	}

	Integer setRowTableHeaders(int sheet, int startRow, int startCol, String [] text) {
		startRow--;startCol--;
		Builder rangeData = RangeData.newBuilder();
		for (int i=0; i<text.length; ++i) {
			CellData data = CellData.newBuilder().setPosition(sally.CellSpaceInformation.newBuilder().setWidth(1).setHeight(1).setPosition( sally.CellPosition.newBuilder().setSheet(sheet).setCol(i+startCol).setRow(startRow).build()).build()).setValue(text[i]).build();
			rangeData.addCells(data);
		}
		return asm.createLegend(LegendCreateData.newBuilder().setFileName("IUI.xls").setItems(rangeData).setParameter(DataParameter.SameContentSameElement).build());
	}

	Integer setColTableHeaders(int sheet, int startRow, int startCol, String [] text) {
		startRow--;startCol--;
		Builder rangeData = RangeData.newBuilder();
		for (int i=0; i<text.length; ++i) {
			CellData data = CellData.newBuilder().setPosition(sally.CellSpaceInformation.newBuilder().setWidth(1).setHeight(1).setPosition( sally.CellPosition.newBuilder().setSheet(sheet).setCol(startCol).setRow(startRow+i).build()).build()).setValue(text[i]).build();
			rangeData.addCells(data);
		}
		return asm.createLegend(LegendCreateData.newBuilder().setFileName("IUI.xls").setItems(rangeData).setParameter(DataParameter.SameContentSameElement).build());
	}

	public void setData() {
		buildPricingSheet();
		buildVendorA();
	}
	
	static final String boltURI="https://tnt.kwarc.info/repos/stc/fcad/flange/cds/nutbolt.omdoc?nutbolt?bolt";
	static final String nutURI="https://tnt.kwarc.info/repos/stc/fcad/flange/cds/ISOhexnut.omdoc?ISOhexnut?ISO-hex-nut";
	static final String gasketURI = "https://tnt.kwarc.info/repos/stc/fcad/flange/cds/flange-bolt-gasket.omdoc?flange-bolt-gasket?flange-gasket";
	static final String flangeURI = "https://tnt.kwarc.info/repos/stc/fcad/flange/cds/flange-bolt-gasket.omdoc?flange-bolt-gasket?flange";
	static final String blindFlangeURI = "https://tnt.kwarc.info/repos/stc/fcad/flange/cds/flange-bolt-gasket.omdoc?flange-bolt-gasket?blind-flange";
	
	static final String partNoURI ="https://tnt.kwarc.info/repos/stc/fcad/flange/cds/partnumber.omdoc?partnumber?part-number";  
	static final String threadTypeURI = "https://tnt.kwarc.info/repos/stc/fcad/flange/cds/ISOmetricthread.omdoc?ISOmetricthread?sISOhexthread";
	static final String colorURI = "https://tnt.kwarc.info/repos/stc/fcad/flange/cds/colors.omdoc?color?color";
	static final String headTypeURI = "https://tnt.kwarc.info/repos/stc/fcad/flange/cds/ISOhexbolt.omdoc?ISOhexbolt?head";
	static final String costURI = "https://tnt.kwarc.info/repos/stc/fcad/flange/cds/cost.omdoc?cost?cost";
	static final String gasketType = "https://tnt.kwarc.info/repos/stc/fcad/flange/cds/flange-bolt-gasket.omdoc?flange-bolt-gasket?gasket-type";
	
	public void buildPricingSheet() {
		Integer workSheetid = asm.getWorksheetIDByName("Pricing");

		Integer tableProps = setRowTableHeaders(workSheetid, 6, 1, new String[] {"Component", "Thread", "Color", "Head", "Type", "Quantity per flange", ""});

		Integer componentCol = setColTableHeaders(workSheetid, 8, 1, new String[] {"bolt", "nut", "gasket", "flange", "blind flange"});
		Integer threadCol = setColTableHeaders(workSheetid, 8, 2, new String[] { "M10", "M10", "_", "M10", "M10"});
		Integer colorCol = setColTableHeaders(workSheetid, 8, 3, new String[] { "black", "black", "_", "black", "black"});
		Integer headCol = setColTableHeaders(workSheetid, 8, 4, new String[] { "machine", "_", "_", "_", "_"});
		Integer typeCol = setColTableHeaders(workSheetid, 8, 5, new String[] { "_", "_", "standard", "_", "_"});
		Integer quantityCol = setColTableHeaders(workSheetid, 8, 6, new String[] { "6", "6", "1", "1", "1"});

		Integer vendorA = setHeaderLabel(workSheetid, 5, 7, 2, "Vendor A");
		Integer vendorB = setHeaderLabel(workSheetid, 5, 9, 2, "Vendor B");
		Integer vendorC = setHeaderLabel(workSheetid, 5, 11, 2, "Vendor C");
		
		Integer costByPieceVendorA = createColFB(workSheetid, 8, 7, new String[] {"0.450 EUR", "0.460 EUR", "0.300 EUR", "0.310 EUR", "0.340 EUR"}, new Integer [] {componentCol, threadCol, colorCol, headCol, typeCol, quantityCol, vendorA});
		Integer costTotalVendorA = createColFB(workSheetid, 8, 8, new String[] {"0.450 EUR", "0.460 EUR", "0.300 EUR", "0.310 EUR", "0.340 EUR"}, new Integer [] {componentCol, threadCol, colorCol, headCol, typeCol, quantityCol, vendorA});
		Integer costByPieceVendorB = createColFB(workSheetid, 8, 9, new String[] {"0.450 EUR", "0.460 EUR", "0.300 EUR", "0.310 EUR", "0.340 EUR"}, new Integer [] {componentCol, threadCol, colorCol, headCol, typeCol, quantityCol, vendorB});
		Integer costTotalVendorB = createColFB(workSheetid, 8, 10, new String[] {"0.450 EUR", "0.460 EUR", "0.300 EUR", "0.310 EUR", "0.340 EUR"}, new Integer [] {componentCol, threadCol, colorCol, headCol, typeCol, quantityCol, vendorB});
		Integer costByPieceVendorC = createColFB(workSheetid, 8, 11, new String[] {"0.450 EUR", "0.460 EUR", "0.300 EUR", "0.310 EUR", "0.340 EUR"}, new Integer [] {componentCol, threadCol, colorCol, headCol, typeCol, quantityCol, vendorC});
		Integer costTotalVendorC = createColFB(workSheetid, 8, 12, new String[] {"0.450 EUR", "0.460 EUR", "0.300 EUR", "0.310 EUR", "0.340 EUR"}, new Integer [] {componentCol, threadCol, colorCol, headCol, typeCol, quantityCol, vendorC});

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
		Integer workSheetid = asm.getWorksheetIDByName("Vendor A");
		
		Integer vendA = setHeaderLabel(workSheetid, 1, 1, 8, "Price List of Vendor A");
		asm.addOntologyLink(vendA, "http://info.kwarc.sissi.winograd/vendor-A");
		
		
		Integer discountMinQuantity = setRowTableHeaders(workSheetid, 4, 1, new String[] {"100", "1000", "10000", ">10000"} );
		Integer discountRatesFB = createRowFB(workSheetid, 5, 1, new String[] {"100.000%", "99.000%", "95.000%", "90.000%"}, new Integer [] {vendA, discountMinQuantity});
		asm.addOntologyLink(discountMinQuantity, "http://info.kwarc.sissi.winograd/discount-min-quantities");
		asm.addOntologyLink(discountRatesFB, "http://info.kwarc.sissi.winograd/discount-rates");
		
		//Integer tableProps = setRowTableHeaders(workSheetid, 7, 1, new String[] {"Part No", "Component", "Thread", "Color", "Head", "Type", "Basic Price"});

		Integer boltsCol = setColTableHeaders(workSheetid, 8, 2, new String[] {"bolt", "bolt", "bolt", "bolt", "bolt", "bolt", "bolt", "bolt"});
		Integer boltThreadCol = setColTableHeaders(workSheetid, 8, 3, new String[] { "M10", "M10", "M10", "M10", "M10", "M10", "M16", "M16"});
		Integer boltColorCol = setColTableHeaders(workSheetid, 8, 4, new String[] { "silver", "silver", "black", "silver", "red", "black", "black", "black"});
		Integer boltHeadCol = setColTableHeaders(workSheetid, 8, 5, new String[] { "carriage", "stove", "machine", "machine", "machine", "machine", "machine", "machine"});
		Integer boltCostCol = setColTableHeaders(workSheetid, 8, 7, new String[] {"0.450 EUR", "0.460 EUR", "0.300 EUR", "0.310 EUR", "0.340 EUR", "0.350 EUR", "0.300 EUR", "0.350 EUR"});
		
		Integer boltPartNo = createColFB(workSheetid, 8, 1, new String[] {"a1", "a2", "a3", "a4", "a5", "a6", "a7", "a8"}, 
				new Integer[]{boltsCol, boltThreadCol, boltColorCol, boltHeadCol, boltCostCol});

		//asm.addOntologyLink(tableProps, "https://tnt.kwarc.info/repos/stc/fcad/flange/cds/component.omdoc?component?ids");
		asm.addOntologyLink(boltPartNo, partNoURI);
		asm.addOntologyLink(boltsCol, boltURI);
		asm.addOntologyLink(boltThreadCol, threadTypeURI);
		asm.addOntologyLink(boltColorCol, colorURI);
		asm.addOntologyLink(boltHeadCol, headTypeURI);
		asm.addOntologyLink(boltCostCol, costURI);


		Integer nutCol = setColTableHeaders(workSheetid, 16, 2, new String[] {"nut", "nut"});
		Integer nutThreadCol = setColTableHeaders(workSheetid, 16, 3, new String[] { "M10", "M16"});
		Integer nutColorCol = setColTableHeaders(workSheetid, 16, 4, new String[] { "black", "black"});
		Integer nutCostCol = setColTableHeaders(workSheetid, 16, 7, new String[] {"0.450 EUR", "0.460 EUR"});
		Integer nutPartNo = createColFB(workSheetid, 16, 1, new String[] {"a9", "a10"}, new Integer[]{nutCol, nutThreadCol, nutColorCol, nutCostCol});

		asm.addOntologyLink(nutCol, nutURI);
		asm.addOntologyLink(nutThreadCol, threadTypeURI);
		asm.addOntologyLink(nutColorCol, colorURI);
		asm.addOntologyLink(nutCostCol, costURI);
		asm.addOntologyLink(nutPartNo, partNoURI);

		Integer gasketCol = setColTableHeaders(workSheetid, 18, 2, new String[] {"gasket"});
		Integer gasketTypeCol = setColTableHeaders(workSheetid, 18, 6, new String[] {"standard"});
		Integer gasketCost = setColTableHeaders(workSheetid, 18, 7, new String[] {"2.040 EUR"});
		Integer gasketPartNo = createColFB(workSheetid, 18, 1, new String[] {"a11"}, new Integer[]{gasketCol, gasketTypeCol, gasketCost});
		
		asm.addOntologyLink(gasketCol, gasketURI);
		asm.addOntologyLink(gasketTypeCol, gasketType);
		asm.addOntologyLink(gasketCost, costURI);
		asm.addOntologyLink(gasketPartNo, partNoURI);

		Integer flangeCol = setColTableHeaders(workSheetid, 19, 2, new String[] {"flange", "flange", "flange"});
		Integer flangeThreadCol = setColTableHeaders(workSheetid, 19, 3, new String[] { "M10", "M10", "M16"});
		Integer flangeColorCol = setColTableHeaders(workSheetid, 19, 4, new String[] { "black", "silver", "black"});
		Integer flangeCostCol = setColTableHeaders(workSheetid, 19, 7, new String[] {"1.080 EUR", "1.080 EUR", "1.090 EUR"});
		Integer flangePartNo = createColFB(workSheetid, 19, 1, new String[] {"a12", "a13", "a14"}, new Integer[]{flangeCol, flangeThreadCol, flangeColorCol, flangeCostCol});

		asm.addOntologyLink(flangeCol, flangeURI);
		asm.addOntologyLink(flangeThreadCol, threadTypeURI);
		asm.addOntologyLink(flangeColorCol, colorURI);
		asm.addOntologyLink(flangeCostCol, costURI);
		asm.addOntologyLink(flangePartNo, partNoURI);

		Integer bindflangeCol = setColTableHeaders(workSheetid, 22, 2, new String[] {"bind-flange", "bind-flange", "bind-flange"});
		Integer bindflangeThreadCol = setColTableHeaders(workSheetid, 22, 3, new String[] { "M10", "M16", "M17"});
		Integer bindflangeColorCol = setColTableHeaders(workSheetid, 22, 4, new String[] { "black", "black", "black"});
		Integer bindflangeCostCol = setColTableHeaders(workSheetid, 22, 7, new String[] {"0.888 EUR", "0.888 EUR", "0.888 EUR"});
		Integer bindflangePartNo = createColFB(workSheetid, 22, 1, new String[] {"a15", "a16", "a17"}, new Integer[]{bindflangeCol, bindflangeThreadCol, bindflangeColorCol, bindflangeCostCol});

		asm.addOntologyLink(bindflangeCol, blindFlangeURI);
		asm.addOntologyLink(bindflangeThreadCol, threadTypeURI);
		asm.addOntologyLink(bindflangeColorCol, colorURI);
		asm.addOntologyLink(bindflangeCostCol, costURI);
		asm.addOntologyLink(bindflangePartNo, partNoURI);
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
			file = new FileOutputStream("iui-model.rdf.64");
			ByteArrayOutputStream so = new ByteArrayOutputStream();
			SpreadsheetModel model = getAsm().serialize();
			model.writeTo(so);
			byte[] b = Base64.encodeBase64(so.toByteArray());
			int off = 0; int len = b.length;
			while (len>0) {
				int toWrite = Math.min(10000, len);
				file.write(b, off, toWrite);
				file.write(new byte[]{10});
				len -= toWrite;
				off += toWrite;
			}

			file.close();

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
		
		Integer workSheetid = t.getAsm().getWorksheetIDByName("Vendor A");
		System.out.println(t.getAsm().getOntologyForPosition(CellPosition.newBuilder().setSheet(workSheetid).setRow(8).setCol(2).build()));
	}
}
